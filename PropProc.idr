module PropProc

import Data.SortedMap
import Data.Vect

import Types.Pushout as Ty
import Queue
import ChannelContext

%default total
%access public export

data Proc : ChanCtx -> Type where
  Done : Proc ctx
  LiftIO : IO () -> Proc ctx -> Proc ctx
  Par : Proc ctx -> Proc ctx -> Proc ctx
  Take : {ctx : ChanCtx} -> (n : names ctx) -> (ty ctx n -> Proc ctx) -> Proc ctx
  Put : {ctx : ChanCtx} -> (n : names ctx) -> (m : ty ctx n) -> Proc ctx -> Proc ctx

-- TODO: Find out if assert_total can be removed.
nameMap : (phi : Morph ctx1 ctx2) -> Proc ctx1 -> Proc ctx2
nameMap phi Done = Done
nameMap phi (LiftIO io p) = LiftIO io (nameMap phi p)
nameMap phi (Par p1 p2) = Par (nameMap phi p1) (nameMap phi p2)
nameMap phi (Put n m p) = Put (mNames phi n) (lemma m) (nameMap phi p)
  where
    lemma m = rewrite sym (law phi n) in m
nameMap phi (Take n resume) = Take (mNames phi n) (assert_total resume')
  where
    resume' x = nameMap phi $ resume (rewrite (law phi n) in x)

record ChanState (ctx : ChanCtx) (n : names ctx) where
  constructor MkChanState
  puts :  Queue (ty ctx n, Proc ctx)
  takes : Queue (ty ctx n -> Proc ctx)

initChanState : ChanState ctx n
initChanState = MkChanState emptyQueue emptyQueue

data MapStates : (ctx : ChanCtx) -> Type where
  MkMapStates : SortedMap (names ctx) (n : (names ctx) ** ChanState ctx n) -> MapStates ctx

get :
  {ctx : ChanCtx} ->
  (DecEq (names ctx)) =>
  MapStates ctx ->
  (n : names ctx) ->
  Maybe (ChanState ctx n)
get {ctx = ctx} (MkMapStates m) n =
  case Data.SortedMap.lookup n m of
    Nothing => Nothing
    Just (n' ** v) =>
      case decEq n n' of
        (Yes Refl) => Just v
        (No contra) => Nothing

-- TODO: don't need to do the deceq, just implement it for all finite sets
put : {ctx : ChanCtx}
   -> MapStates ctx
   -> (n : names ctx)
   -> (ChanState ctx n)
   -> MapStates ctx
put {ctx = ctx} (MkMapStates m) n s = MkMapStates (insert n (n ** s) m)

step :
  {ctx : ChanCtx} ->
  (DecEq (names ctx)) =>
  (MapStates ctx) ->
  Queue (Proc ctx) ->
  IO (Maybe (MapStates ctx, Queue (Proc ctx)))
step {ctx} chanStates jobs = do
  case deq jobs of
    Nothing => do putStrLn "No more jobs."
                  pure Nothing
    Just (j, jobs') =>
      case j of
        Done =>
          pure $ Just (chanStates, jobs')
        LiftIO io next => do
          io
          pure $ Just (chanStates, enq next jobs')
        Par j1 j2 =>
          pure $ Just (chanStates, enqs jobs' [j1, j2])
        Take n resumeTake => do
          --putStrLn "TAKE"
          case get chanStates n of
            Nothing => pure Nothing
            Just c =>
              case deq (puts c) of
                Nothing =>
                  pure $ Just (put chanStates n (record {takes $= enq resumeTake} c), jobs')
                Just ((x, resumePut), newPuts) =>
                  pure $ Just (put chanStates n (record {puts = newPuts} c), enqs jobs' [resumePut, resumeTake x])
        Put n x resumePut => do
          --putStrLn "PUT"
          case get chanStates n of
            Nothing => do putStrLn "error: channel didn't exist."
                          pure Nothing
            Just c =>
              case deq (takes c) of
                Nothing => do
                  --putStrLn "  No takes."
                  pure $ Just (put chanStates n (record {puts $= enq (x, resumePut)} c), jobs')
                Just (resumeTake, newTakes) => do
                  --putStrLn "There was a taker."
                  pure $ Just (put chanStates n (record {takes = newTakes} c), enqs jobs' [resumeTake x, resumePut])

partial
steps :
  {ctx : ChanCtx} ->
  (DecEq (names ctx)) =>
  (MapStates ctx) ->
  Queue (Proc ctx) ->
  IO ()
steps {ctx} initState jobs = do
  Just (newState, newJobs) <- step initState jobs | _ => putStrLn "END"
  steps newState newJobs

----
-- the props compositions
----

-- First we need pushouts of ChanCtx

{-
-- TODO: we need the pushout to contain the commuting triangle laws.
pushoutChanCtx :
  {a,b,c : ChanCtx} ->
  (f : MorphChanCtx c a) ->
  (g : MorphChanCtx c b) ->
  (d : ChanCtx ** (MorphChanCtx a d, MorphChanCtx b d))
pushoutChanCtx
    {a} {b} {c}
    (MkMorphChanCtx mapNamesF _)
    (MkMorphChanCtx mapNamesG _) =
  case pushout mapNamesF mapNamesG of
    pu@(MkPU n labs inL inR _) =>
      let d = MkChanCtx (MkFinSet n labs) (uniProp pu Type (ty a) (ty b))
      in (d ** (MkMorphChanCtx inL ?law1, MkMorphChanCtx inR ?law2))
-}

data PropProc:
    (apex: ChanCtx) ->
    (ins: ChanCtx) ->
    (outs: ChanCtx) ->
    (inM: Morph ins apex) ->
    (outsM: Morph outs apex) ->
    Type where
  MkPropProc: Proc apex -> PropProc apex ins outs inM outM

{-
||| Equipment needed to compose to PropProc.
data CompEquip: (p1 : PropProc t1 a b) -> (p2 : PropProc t2 b c) -> Type where
  MkCompEquip:
    Pushout (outM p1) (inM p2) -> CompEquip p1 p2

apexComp : CompEquip p1 p2 -> ChanCtx
apexComp (MkCompEquip pu) = let (apex ** _) = span pu in apex
-}

propComp:
  {apex1, apex2, a, b, c: ChanCtx} ->
  (p1 : PropProc apex1 a b in1 out1) ->
  (p2 : PropProc apex2 b c in2 out2) ->
  (pu : Pushout out1 in2 apex u v) ->
        PropProc apex  a c (comp in1 u) (comp out2 v)
propComp
    {u} {v}
    (MkPropProc proc1)
    (MkPropProc proc2)
    pu =
  let proc1' = nameMap u proc1
      proc2' = nameMap v proc2
  in MkPropProc (Par proc1' proc2')

mkInitState : Ord (names apex) => List (names apex) -> MapStates apex
mkInitState xs =
  MkMapStates
    (fromList (map (\e => (e, (e ** initChanState))) xs))

partial
runner :
  (Ord (names apex)) =>
  (DecEq (names apex)) =>
  List (names apex) ->
  PropProc apex a b inM outM -> IO ()
runner xs (MkPropProc proc) = do
  let initSt = mkInitState xs
  putStrLn "BEGIN"
  steps initSt (enqs emptyQueue [proc])

--

transfer : PropProc apex ins outs inM outM -> PropProc apex ins' outs' inM' outM'
transfer (MkPropProc p) = MkPropProc p

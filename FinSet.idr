module FinSet

import Data.Vect
import Data.Fin
import Data.SortedMap
import Data.SortedSet
import Control.Monad.State
import Debug.Trace

%default total
%access public export

finsV : (n : Nat) -> Vect n (Fin n)
finsV Z = []
finsV (S k) = FZ :: (map FS (finsV k))

fins : (n : Nat) -> List (Fin n)
fins n = toList (finsV n)

||| Finite sets with named elements
data FinSet : Type where
  MkFinSet : (n : Nat) -> Vect n String -> FinSet

data ElemFS : FinSet -> Type where
  MkElemFS : Fin n -> ElemFS (MkFinSet n labels)

elemsList : (fs: FinSet) -> List (ElemFS fs)
elemsList (MkFinSet n xs) = map MkElemFS (fins n)

Eq (ElemFS x) where
  (MkElemFS i) == (MkElemFS j) = i == j

Ord (ElemFS x) where
  compare (MkElemFS i) (MkElemFS j) = compare i j

DecEq (ElemFS x) where
  decEq (MkElemFS i) (MkElemFS j) = case decEq i j of
    (Yes Refl) => Yes Refl
    (No contra) => No (\Refl => contra Refl)

elem : (label : String) -> {auto pf : Elem label labels} -> ElemFS (MkFinSet n labels)
elem label {pf = Here} = MkElemFS FZ
elem label {pf = (There later)} with (elem label {pf = later})
  | (MkElemFS i) = MkElemFS (FS i)

data MorphFS : FinSet -> FinSet -> Type where
  MkMorphFS : Vect n1 (ElemFS target)-> MorphFS (MkFinSet n1 ls1) target

mapElem : (f : MorphFS x y) -> ElemFS x -> ElemFS y
mapElem (MkMorphFS ass) (MkElemFS i) = index i ass

compFS : {a,b,c: FinSet} -> MorphFS a b -> MorphFS b c -> MorphFS a c
compFS {a = MkFinSet na la} {b = MkFinSet nb lb} {c = c} (MkMorphFS xs) (MkMorphFS ys) =
  MkMorphFS (map (\(MkElemFS i) => Data.Vect.index i ys) xs)

-- examples

{-
Employees : FinSet
Employees = MkFinSet 2 ["alice", "bob"]

alice: ElemFS Employees
alice = elem "alice"
bob: ElemFS Employees
bob = elem "bob"

Desks : FinSet
Desks = MkFinSet 3 ["desk1", "desk2", "desk3"]

assignment : MorphFS Employees Desks
assignment = MkMorphFS [elem "desk2", elem "desk1"]
-}

-- Pushouts

record Graph a where
  constructor MkGraph
  points : List a
  edges : List (a,a)

tuple : (a -> b) -> (a,a) -> (b,b)
tuple f (x,y) = (f x, f y)

||| get a minimal set of nodes forming covering set of representatives of
||| connected components.
reduce : (Ord a) => Graph a -> State (SortedMap a a) (List a)
reduce (MkGraph points []) = pure points
reduce (MkGraph points ((x, y) :: es)) = assert_total $
    do -- we remove the edge (x,y)
       points' <- reduce (MkGraph points es)
       repls <- get
       let new_x = fromMaybe x (SortedMap.lookup x repls)
       let new_y = fromMaybe y (SortedMap.lookup y repls)
       if x == y
         then pure points' -- x and y have already been identified
         else do -- we throw away y
                 let newPoints = filter (/= new_y) points'
                 let newRepls = the (SortedMap a a) (fromList [ (u, rep new_y new_x v) | (u,v) <- toList repls ])
                 put newRepls
                 pure newPoints
  where
    rep : (Ord b) => b -> b -> b -> b
    rep a b p = if p == a then b else p

reduce' : (Ord a) => Graph a -> (List a, List (a,a))
reduce' g@(MkGraph points edges) =
  let (ps, repls) = runState (reduce g) (fromList [ (x,x) | x <- points ])
  in (ps, toList repls)

firstFree : SortedSet String -> String -> String
firstFree used lab =
    if SortedSet.contains lab used
      then firstFree' 1 used lab
      else lab
  where
    firstFree' : Int -> SortedSet String -> String -> String
    firstFree' n used lab =
      if contains (lab ++ show n) used
        then assert_total $ firstFree' (n+1) used lab
        else lab ++ show n

labelsLR : Vect na String -> Vect nb String -> Vect k (Either (Fin na) (Fin nb)) -> Vect k String
labelsLR = labelsLR' SortedSet.empty
  where
    labelsLR' : SortedSet String -> Vect na String -> Vect nb String -> Vect k (Either (Fin na) (Fin nb)) -> Vect k String
    labelsLR' used lefts rights [] = []
    labelsLR' used lefts rights ((Left l) :: xs) =
      let lab = index l lefts
          lab' = firstFree used lab
      in lab' :: labelsLR' (insert lab' used) lefts rights xs
    labelsLR' used lefts rights ((Right r) :: xs) =
      let lab = index r rights
          lab' = firstFree used lab
      in lab' :: labelsLR' (insert lab' used) lefts rights xs

(Ord a, Ord b) => Ord (Either a b) where
  compare (Left l1) (Left l2) = compare l1 l2
  compare (Left l) (Right r) = LT
  compare (Right r) (Left l) = GT
  compare (Right r1) (Right r2) = compare r1 r2

getIndexOf : String -> String -> (n : Nat) -> (Either (Fin na) (Fin nb)) -> List (Either (Fin na) (Fin nb)) -> Either String (Fin n)
getIndexOf d d' Z x xs = Left $ "couldn't find: " ++ d ++ " in: " ++ d'
getIndexOf d d' (S k) x [] = Left $ "couldnt' find: " ++ d ++ " in: " ++ d'
getIndexOf d d' (S k) x (y :: xs) =
  if x == y
    then Right FZ
    else FS <$> getIndexOf d d' k x xs

lookupE : Either (Fin na) (Fin nb) -> SortedMap (Either (Fin na) (Fin nb)) v -> Either String v
lookupE k m = case lookup k m of
  Just v => Right v
  Nothing => Left $ "couldn't find value in map" --Prelude.Strings.++ (show k) Prelude.Strings.++ " in the map."

showEFins : Either (Fin na) (Fin nb) -> String
showEFins (Left l) = "Left " ++ show (finToInteger l)
showEFins (Right r) = "Right " ++ show (finToInteger r)

data PushOut : {a,b,c: FinSet} ->
               (f : MorphFS c a) ->
               (g : MorphFS c b) ->
               Type where
  MkPU : (n : Nat) ->
         (labs : Vect n String) ->
         (MorphFS a (MkFinSet n labs))->
         (MorphFS b (MkFinSet n labs)) ->
         (Vect n (Either (ElemFS a) (ElemFS b))) ->
         PushOut {a=a} {b=b} {c=c} f g

pushout' :
  {a,b,c: FinSet} ->
  (f : MorphFS c a) ->
  (g : MorphFS c b) ->
  Either String
  (PushOut f g)
pushout'
  {a = MkFinSet na xs}
  {b = MkFinSet nb ys}
  {c = MkFinSet nc zs}
  f
  g =
    let elemsL  = map Left (fins na)
        elemsR  = map Right (fins nb)
        elemsLR = elemsL ++ elemsR
        (elems, repls) = runState (reduce (MkGraph elemsLR (map makeEdge (fins nc)))) (fromList [ (x,x) | x <- elemsLR ])
        n = length elems
        elemsV = the (Vect n (Either (Fin na) (Fin nb))) (fromList elems)
        labelsV =  labelsLR xs ys elemsV
        d = MkFinSet n labelsV
    in do inL <- the (Either String (Vect na (Fin n)))
                     (traverse (\i => do new <- lookupE (Left i) repls
                                         getIndexOf (showEFins new) (show (map showEFins elems)) n new elems)
                               (finsV na))
          inR <- the (Either String (Vect nb (Fin n)))
                     (traverse (\j => do new <- lookupE (Right j) repls
                                         getIndexOf (showEFins new) (show (map showEFins elems)) n new elems)
                               (finsV nb))
          pure (MkPU n
                     labelsV
                     (MkMorphFS (map MkElemFS inL))
                     (MkMorphFS (map MkElemFS inR))
                     (map fff elemsV)
               )
  where
    fff : Either (Fin na) (Fin nb) -> Either (ElemFS (MkFinSet na xs)) (ElemFS (MkFinSet nb ys))
    fff (Left l) = Left (MkElemFS l)
    fff (Right r) = Right (MkElemFS r)

    makeEdge : Fin nc -> (Either (Fin na) (Fin nb), Either (Fin na) (Fin nb))
    makeEdge i =
      case (mapElem f (MkElemFS i), mapElem g (MkElemFS i)) of
        (MkElemFS j, MkElemFS k) => (Left j, Right k)

-- TODO: make the above function total
pushout :
  {a,b,c: FinSet} ->
  (f : MorphFS c a) ->
  (g : MorphFS c b) ->
  PushOut f g
pushout {a} {b} {c} f g = assert_total $
  case pushout' f g of
    Right pu => pu

pushOutSet : PushOut f g -> FinSet
pushOutSet (MkPU n labs inL inR xs) = MkFinSet n labs

uniProp : {a,b,c : FinSet} ->
          {f : MorphFS c a} ->
          {g : MorphFS c b} ->
          (pu : PushOut {a=a} {b=b} {c=c} f g) ->
          (t : Type) ->
          (u : ElemFS a -> t) ->
          (v : ElemFS b -> t) ->
          (ElemFS (pushOutSet pu) -> t)
uniProp {a = a} {b = b} {c = c} {f = f} {g = g} (MkPU n labs inL inR code) t u v (MkElemFS i) =
  case index i code of
    Left l => u l
    Right r => v r

--

SetA : FinSet
SetA = MkFinSet 3 ["a", "b", "c"]

SetB : FinSet
SetB = MkFinSet 3 ["alpha", "beta", "gamma"]

SetC : FinSet
SetC = MkFinSet 2 ["1", "2"]

Mf : MorphFS SetC SetA
Mf = MkMorphFS [elem "b", elem "c"]


Mg : MorphFS SetC SetB
Mg = MkMorphFS [elem "beta", elem "beta"]

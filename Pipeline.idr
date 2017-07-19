module Pipeline

import Types.Pushout as Ty
import ChannelContext
import PropProc
import Examples.PingPong as PingPong

-- First the context of a pipline of length n
IntPipeCh : (n: Nat) -> ChanCtx
IntPipeCh n = (MkChanCtx (Pipeline n) (const Int))

||| Pipe of length 0
IntCh : ChanCtx
IntCh = IntPipeCh 0

-- some morphisms which will be useful:

InInt : {n: Nat} -> Morph IntCh (IntPipeCh n)
InInt = MkMorph InM (\_ => Refl)

OutInt : {n: Nat} -> Morph IntCh (IntPipeCh n)
OutInt = MkMorph OutM (\_ => Refl)

ButLastInt : (n : Nat) -> Morph (IntPipeCh n) (IntPipeCh (S n))
ButLastInt n = MkMorph ButLast (\_ => Refl)

LastInt : (n : Nat) -> Morph (IntPipeCh 1) (IntPipeCh (S n))
LastInt n = MkMorph Last (\_ => Refl)

IntPipe : (n : Nat) -> Type
IntPipe n =
  PropProc (IntPipeCh n)
           (IntPipeCh 0) (IntPipeCh 0)
           InInt
           OutInt

-- We make a higher order function which chains integer pipelines together

connect :
  {n: Nat} ->
  IntPipe n ->
  IntPipe 1 ->
  PropProc (IntPipeCh (S n)) IntCh IntCh (comp InInt (ButLastInt n)) (comp OutInt (LastInt n))
connect {n} pipe1 pipe2 = propComp pipe1 pipe2 (MkPushout (addStep n))

infixl 5 ~>~
(~>~) : {n: Nat} -> IntPipe n -> IntPipe 1 -> IntPipe (S n)
(~>~) {n} pipe1 pipe2 = transfer (connect pipe1 pipe2)

addProducer : {n:Nat} -> PropProc IntCh IntCh IntCh IdMorph IdMorph -> IntPipe n -> IntPipe n
addProducer {n} prod pipe = transfer p
  where
    p : PropProc (IntPipeCh n) IntCh IntCh (comp IdMorph InInt) (comp OutInt IdMorph)
    p = propComp prod pipe (MkPushout (identityLeft (Pipeline 0) (Pipeline n) InM))

addConsumer : {n:Nat} -> IntPipe n ->  PropProc IntCh IntCh IntCh IdMorph IdMorph -> IntPipe n
addConsumer {n} pipe cons = transfer p
  where
    p : PropProc (IntPipeCh n) IntCh IntCh (comp InInt IdMorph) (comp IdMorph OutInt)
    p = propComp pipe cons (MkPushout (identityRight (Pipeline 0) (Pipeline n) OutM))

-- EXAMPLES

incrementer : IntPipe 1
incrementer = MkPropProc p
  where
    p : Proc (IntPipeCh 1)
    p = Take In
          (\i => Put Out (i+1) p)

incrementThrice : IntPipe 3
incrementThrice = incrementer ~>~ incrementer ~>~ incrementer

-- produces the integers 1 to 10
produce1to10 : PropProc IntCh IntCh IntCh IdMorph IdMorph
produce1to10 = MkPropProc (go 0)
  where
    go : Int -> Proc IntCh
    go n = Put In n
               (if n < 10
                  then go (n+1)
                  else Done)

-- consumes integers until it finds one >= 10
partial
consumeLessThan10 : PropProc IntCh IntCh IntCh IdMorph IdMorph
consumeLessThan10 = MkPropProc go
  where
    partial
    go : Proc IntCh
    go = Take In
           (\i =>
              LiftIO (putStrLn $ "Consumed: " ++ show i)
                     (if i < 10
                        then go
                        else Done))

proc : IntPipe 3
proc = addProducer produce1to10 (addConsumer incrementThrice consumeLessThan10)

main : IO ()
main =
  --runner [exchPnt] prodCons
  --runner [In, Out] prodIncrCons
  -- PingPong.main
  runner [In, NextStep In, NextStep (NextStep In), NextStep (NextStep (NextStep In))] proc

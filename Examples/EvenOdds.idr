module Examples.EvenOdds

import Types.Pushout as Ty
import ChannelContext
import PropProc

data InOut a b = InCh a | OutCh b

-- forms the coproduct of two channel contexts
Coproduct : ChanCtx -> ChanCtx -> ChanCtx
Coproduct (MkChanCtx ns1 ty1) (MkChanCtx ns2 ty2) =
    MkChanCtx (InOut ns1 ns2) ty
  where
    ty (InCh x)  = ty1 x
    ty (OutCh x) = ty2 x

InM : (a: ChanCtx) -> (b: ChanCtx) -> Morph a (Coproduct a b)
InM (MkChanCtx ns1 ty1) (MkChanCtx ns2 ty2) = MkMorph InCh (\x => Refl)

OutM : (a: ChanCtx) -> (b: ChanCtx) -> Morph b (Coproduct a b)
OutM (MkChanCtx ns1 ty1) (MkChanCtx ns2 ty2) = MkMorph OutCh (\x => Refl)

IntCh : ChanCtx
IntCh = MkChanCtx () (const Int)

data Parity = Even | Odd

ParityCh : ChanCtx
ParityCh = MkChanCtx Parity (const Int)

-- we make a process adds 3 to integers, and then puts them onto two different
-- channels, one for if the original integer was even, and another for if it was
-- odd.

procA : PropProc (Coproduct IntCh ParityCh) IntCh ParityCh (InM IntCh ParityCh) (OutM IntCh ParityCh)
procA = MkPropProc $ go
  where
    go = Take (InCh ())
           (\i => if mod i 2 == 0
                  then Put (OutCh Even) (i+3) go
                  else Put (OutCh Odd) (i+3) go)

-- We have another process which increments integers.

procB : PropProc (Coproduct IntCh IntCh) IntCh IntCh (InM IntCh IntCh) (OutM IntCh IntCh)
procB = MkPropProc $ go
  where
    go = Take (InCh ())
           (\i => Put (OutCh ()) (i+1) go)

-- Now we want to pipeline these two processes together. We are very interested
-- in the "add 3" feature of procA, but don't care at all about the splitting
-- into evens and odds. So we need a special pushout in order to mesh these two
-- processes together.

namespace TwoStep

  data TwoStep = In | Middle | Out

InL : InOut () Parity -> TwoStep
InL (InCh ()) = In
InL (OutCh _) = Middle

InR : InOut () () -> TwoStep
InR (InCh ()) = Middle
InR (OutCh ()) = Out

pu : Pushout OutCh (const (InCh ())) TwoStep InL InR
pu = MkPushout uniProp
  where
    uniProp t l r pf = (lr ** (ll, rr))
      where lr : TwoStep -> t
            lr TwoStep.In = l (InCh ())
            lr Middle = r (InCh ())
            lr Out = r (OutCh ())

            ll (InCh ()) = Refl
            ll (OutCh x) = pf x -- we need to use the proof in the case we took
                                -- an arbitrary choice.

            rr (InCh ()) = Refl
            rr (OutCh ()) = Refl

-- now we can make our big process

Ctx : ChanCtx
Ctx = MkChanCtx TwoStep (const Int)

proc : PropProc Ctx IntCh IntCh ?lol1 ?lol2
proc = propComp procA procB' (MkPushout pu)
  where
    -- we need to collapse procAs output into procBs:
    Collapse : Morph ParityCh IntCh
    Collapse = MkMorph (const ()) (\_ => Refl)

    procB' : PropProc (Coproduct IntCh IntCh) ParityCh IntCh (comp Collapse (InM IntCh IntCh)) (OutM IntCh IntCh)
    procB' = transfer procB

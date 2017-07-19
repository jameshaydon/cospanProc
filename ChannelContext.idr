||| Typed channel context of a process.
module ChannelContext

import Types.Pushout as Ty

%default total
%access public export

||| A channel context is a set (type) of names, together with a type associated
||| to each name.
public export
record ChanCtx where
  constructor MkChanCtx
  names : Type
  ty : (n : names) -> Type

||| A morphism of channel contexts is a mapping of the names that preserves the
||| typing structure.
public export
record Morph (ctx1 : ChanCtx) (ctx2 : ChanCtx) where
  constructor MkMorph
  mNames : names ctx1 -> names ctx2
  law : (n : names ctx1) -> ty ctx1 n = ty ctx2 (mNames n)

IdMorph : {ctx : ChanCtx} -> Morph ctx ctx
IdMorph = MkMorph id (\n => Refl)

||| Composition of morphisms of channels contexts.
lawComp : (a : ChanCtx) -> (b : ChanCtx) -> (c : ChanCtx) -> (m1 : names a -> names b) -> (l1 : (n : names a) -> ty a n = ty b (m1 n)) -> (m2 : names b -> names c) -> (l2 : (n : names b) -> ty b n = ty c (m2 n)) -> (n : names a) -> ty a n = ty c ((m2 . m1) n)
lawComp a b c m1 l1 m2 l2 n =
  let step1 = l1 n
      step2 = l2 (m1 n)
  in trans step1 step2

comp :
  {a,b,c: ChanCtx} ->
  Morph a b ->
  Morph b c ->
  Morph a c
comp  {a = a} {b = b} {c = c}
      (MkMorph m1 l1)
      (MkMorph m2 l2) =
    MkMorph (m2 . m1) (lawComp a b c m1 l1 m2 l2)

data Pushout:
    (f : Morph base left) ->
    (g : Morph base right) ->
    (apex : ChanCtx) ->
    (inL : Morph left apex) ->
    (inR : Morph right apex) ->
    Type where
  MkPushout:
    (Ty.Pushout fN gN nA inLN inRN) ->
    Pushout (MkMorph fN fL) (MkMorph gN gL) (MkChanCtx nA tyA) (MkMorph inLN inLL) (MkMorph inRN inRL)

{-
span:
  {base, left, right : ChanCtx} ->
  {f : Morph base left} ->
  {g : Morph base right} ->
  Pushout f g a ->
  (Morph left a, Morph right a)
span (MkPushout (MkPushout inL inR uniProp)) =
    let (lr ** (comL, comR)) = uniProp Type (ty left) (ty right) pf
    in (MkMorph inL (\x => ?ll), MkMorph inR ?rr)
  where
    pf : (x : names base) -> ty left (mNames f x) = ty right (mNames g x)
    pf x = let step1 = sym (law f x)
               step2 = law g x
           in trans step1 step2

-}


-- inL:
--   {base, left, right : ChanCtx} ->
--   {f : Morph base left} ->
--   {g : Morph base right} ->
--   Pushout f g ->

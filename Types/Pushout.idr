module Types.Pushout

%default total
%access public export

||| A Pushout for the category `Type`.
data Pushout:
    (f : base -> left) ->
    (g : base -> right) ->
    (pu : Type) ->
    (inL : left -> pu) ->
    (inR : right -> pu) ->
    Type where
  MkPushout :
    {pu: Type} ->
    {inL : left -> pu} ->
    {inR : right -> pu} ->
    ( uniProp: (t : Type) ->
               (l : left -> t) ->
               (r : right -> t) ->
               (pf : (x : base) -> l (f x) = r (g x) ) ->
               (lr : (pu -> t) ** ((x : left) -> l x = lr (inL x), (x : right) -> r x = lr (inR x))) ) ->
    Pushout {base=base} {left=left} {right=right} f g pu inL inR

-- Examples

||| Pushout with the identity on the left
identityLeft : (a : Type) -> (b : Type) -> (f : a -> b) ->
  Pushout Basics.id f b f Basics.id
identityLeft a b f = MkPushout (\t, l, r, pf => (r ** (pf, \x => Refl)))

||| Pushout with the identity on the right
identityRight : (a : Type) -> (b : Type) -> (f : a -> b) ->
  Pushout f Basics.id b Basics.id f
identityRight a b f = MkPushout (\t, l, r, pf => (l ** (\x => Refl, \x => sym (pf x))))

-- Pipelines!

data Pipeline : (n : Nat) -> Type where
  In: Pipeline k
  NextStep: Pipeline k -> Pipeline (S k)

NextStepInjective : (p : Pipeline k) -> (q : Pipeline k) -> NextStep p = NextStep q -> p = q
NextStepInjective left _ Refl = Refl

InNotNextStep : {n : Nat} -> {p : Pipeline k} -> In {k = n} = NextStep p -> Void
InNotNextStep Refl impossible

DecEq (Pipeline n) where
  decEq In In = Yes Refl
  decEq In (NextStep p) = No InNotNextStep
  decEq (NextStep p) In = No (negEqSym InNotNextStep)
  decEq (NextStep p) (NextStep q) with (decEq p q)
    | Yes prf = Yes (cong prf)
    | No contra = No (\h => contra (NextStepInjective p q h))

Eq (Pipeline n) where
  (==) In In = True
  (==) (NextStep p) (NextStep q) = p == q
  (==) _ _ = False

Ord (Pipeline n) where
  compare In In = EQ
  compare In (NextStep _) = LT
  compare (NextStep p) In = GT
  compare (NextStep p) (NextStep q) = compare p q

Out : {n: Nat} -> Pipeline n
Out {n= Z} = In
Out {n= S k} = NextStep Out

InM : Pipeline 0 -> Pipeline n
InM = const In

OutM : Pipeline 0 -> Pipeline n
OutM = const Out

ButLast : Pipeline n -> Pipeline (S n)
ButLast {n = n} In = In
ButLast {n = S k} (NextStep step) = NextStep (ButLast step)

Last : Pipeline (S Z) -> Pipeline (S n)
Last In = ButLast Out
Last (NextStep x) = Out

-- we show that adding one step to a (n)-pipeline makes an (n+1)-pipeline.

ppp :
  (k : Nat) ->
  (l : Pipeline (S k) -> t) ->
  (r : Pipeline 1 -> t) ->
  (pf : (x : Pipeline 0) -> l (OutM x) = r (InM x)) ->
  (x : Pipeline (S k)) ->
  (x1 : Pipeline 0) ->
  (l . NextStep) (OutM x1) = r (InM x1)
ppp k l r pf x In = pf In

lr :
  (n : Nat) ->
  (t : Type) ->
  (l : Pipeline n -> t) ->
  (r : Pipeline (S Z) -> t) ->
  (pf: (x : Pipeline 0) -> l (OutM x) = r (InM x)) ->
  (Pipeline (S n) -> t)
lr Z t l r pf x = r x
lr (S k) t l r pf In = l In
lr (S k) t l r pf (NextStep x) = lr k t (l . NextStep) r (ppp k l r pf x) x

uu1 :
  (t : Type) ->
  (l : Pipeline n -> t) ->
  (r : Pipeline (S Z) -> t) ->
  (pf : (x : Pipeline 0) -> l (OutM x) = r (InM x)) ->
  (x20 : Pipeline n) ->
  l x20 = lr n t l r pf (ButLast x20)
uu1 {n = Z} t l r pf In = pf In
uu1 {n = (S k)} t l r pf In = Refl
uu1 {n = (S k)} t l r pf (NextStep x) =
  uu1 {n=k} t (l . NextStep) r (ppp k l r pf (ButLast x)) x

uu2 :
  (t : Type) ->
  (l : Pipeline n -> t) ->
  (r : Pipeline 1 -> t) ->
  (pf : (x : Pipeline 0) -> l (OutM x) = r (InM x)) ->
  (x21 : Pipeline 1) ->
  r x21 = lr n t l r pf (Last x21)
uu2 {n = Z} t l r pf In = Refl
uu2 {n = Z} t l r pf (NextStep In) = Refl
uu2 {n = (S k)} t l r pf In =
  let yyy = sym (pf In)
  in trans yyy (uu1 {n = k} t (l . NextStep) r (ppp k l r pf (ButLast Out)) Out)
uu2 {n = (S k)} t l r pf (NextStep In) =
  uu2 {n=k} t (l . NextStep) r (ppp k l r pf (NextStep Out)) (NextStep In)

addStep:
  (n: Nat) ->
  Pushout {base = Pipeline Z}
          {left = Pipeline n}
          {right = Pipeline (S Z)}
          OutM
          InM
          (Pipeline (S n))
          ButLast
          Last
addStep n = MkPushout uni
  where
    uni t l r pf = ((lr n t l r pf) ** (uu1 t l r pf, uu2 t l r pf))

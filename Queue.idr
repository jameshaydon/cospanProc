module Queue

%default total
%access export

data Queue : Type -> Type where
  MkQueue :
    (front : List a) ->
    (back : List a) ->
    Queue a

emptyQueue : {a : Type} -> Queue a
emptyQueue = MkQueue [] []

enq : (x : a) -> (q : Queue a) -> Queue a
enq x (MkQueue front back) = MkQueue front (x :: back)

enqs : (q : Queue a) -> (xs : List a) -> Queue a
enqs = foldr enq

deq : (q : Queue a) -> Maybe (a, Queue a)
deq (MkQueue [] back) = case reverse back of
  [] => Nothing
  (f :: fs) => Just (f, MkQueue fs [])
deq (MkQueue (f :: fs) back) = Just (f, MkQueue fs back)

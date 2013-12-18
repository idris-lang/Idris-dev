module Control.Isomorphism

import Syntax.PreorderReasoning

%default total

-- An isomorphism between two types
data Iso : Type -> Type -> Type where
  MkIso : (to : a -> b) ->
          (from : b -> a) ->
          (toFrom : (y : b) -> to (from y) = y) ->
          (fromTo : (x : a) -> from (to x) = x) ->
          Iso a b

-- Isomorphism properties

isoRefl : Iso a a
isoRefl = MkIso id id (\x => refl) (\x => refl)

isoTrans : Iso a b -> Iso b c -> Iso a c
isoTrans (MkIso to from toFrom fromTo) (MkIso to' from' toFrom' fromTo') =
  MkIso (\x => to' (to x))
        (\y => from (from' y))
        (\y => (to' (to (from (from' y))))  ={ cong (toFrom (from' y)) }=
               (to' (from' y))              ={ toFrom' y }=
               y QED)
        (\x => (from (from' (to' (to x))))  ={ cong (fromTo' (to x)) }=
               (from (to x))                ={ fromTo x }=
               x QED)



-- Isomorphisms over sums

eitherComm : Iso (Either a b) (Either b a)
eitherComm = MkIso swap swap swapSwap swapSwap
  where swap : Either a b -> Either b a
        swap (Left x) = Right x
        swap (Right x) = Left x
        swapSwap : (e : Either a b) -> swap (swap e) = e
        swapSwap (Left x) = refl
        swapSwap (Right x) = refl

eitherAssoc : Iso (Either (Either a b) c) (Either a (Either b c))
eitherAssoc = MkIso eitherAssoc1 eitherAssoc2 ok1 ok2
  where eitherAssoc1 : Either (Either a b) c -> Either a (Either b c)
        eitherAssoc1 (Left (Left x)) = Left x
        eitherAssoc1 (Left (Right x)) = Right (Left x)
        eitherAssoc1 (Right x) = Right (Right x)

        eitherAssoc2 : Either a (Either b c) -> Either (Either a b) c
        eitherAssoc2 (Left x) = Left (Left x)
        eitherAssoc2 (Right (Left x)) = Left (Right x)
        eitherAssoc2 (Right (Right x)) = Right x

        ok1 : (x : Either a (Either b c)) -> eitherAssoc1 (eitherAssoc2 x) = x
        ok1 (Left x) = refl
        ok1 (Right (Left x)) = refl
        ok1 (Right (Right x)) = refl

        ok2 : (x : Either (Either a b) c) -> eitherAssoc2 (eitherAssoc1 x) = x
        ok2 (Left (Left x)) = refl
        ok2 (Left (Right x)) = refl
        ok2 (Right x) = refl

eitherBotLeft : Iso (Either _|_ a) a
eitherBotLeft = MkIso to from ok1 ok2
  where to : Either _|_ a -> a
        to (Left x) = FalseElim x
        to (Right x) = x
        from : a -> Either _|_ a
        from = Right
        ok1 : (x : a) -> to (from x) = x
        ok1 x = refl
        ok2 : (x : Either _|_ a) -> from (to x) = x
        ok2 (Left x) = FalseElim x
        ok2 (Right x) = refl

eitherBotRight : Iso (Either a _|_) a
eitherBotRight = isoTrans eitherComm eitherBotLeft

-- Isomorphisms over products
pairComm : Iso (a, b) (b, a)
pairComm = MkIso swap swap swapSwap swapSwap
  where swap : (a, b) -> (b, a)
        swap (x, y) = (y, x)
        swapSwap : (x : (a, b)) -> swap (swap x) = x
        swapSwap (x, y) = refl

pairAssoc : Iso (a, (b, c)) ((a, b), c)
pairAssoc = MkIso to from ok1 ok2
  where
    to : (a, (b, c)) -> ((a, b), c)
    to (x, (y, z)) = ((x, y), z)
    from : ((a, b), c) -> (a, (b, c))
    from ((x, y), z) = (x, (y, z))
    ok1 : (x : ((a, b), c)) -> to (from x) = x
    ok1 ((x, y), z) = refl
    ok2 : (x : (a, (b, c))) -> from (to x) = x
    ok2 (x, (y, z)) = refl

pairUnitRight : Iso (a, ()) a
pairUnitRight = MkIso fst (\x => (x, ())) (\x => refl) ok
  where ok : (x : (a, ())) -> (fst x, ()) = x
        ok (x, ()) = refl

pairUnitLeft : Iso ((), a) a
pairUnitLeft = isoTrans pairComm pairUnitRight

pairBotLeft : Iso (_|_, a) _|_
pairBotLeft = MkIso fst FalseElim (\x => FalseElim x) (\y => FalseElim (fst y))

pairBotRight : Iso (a, _|_) _|_
pairBotRight = isoTrans pairComm pairBotLeft


-- Enable preorder reasoning syntax over isomorphisms
qed : (a : Type) -> Iso a a
qed a = isoRefl

step : (a : Type) -> Iso a b -> Iso b c -> Iso a c
step a iso1 iso2 = isoTrans iso1 iso2

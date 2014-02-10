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
               (to' (from' y))              ={ toFrom' y               }=
               y                            QED)
        (\x => (from (from' (to' (to x))))  ={ cong (fromTo' (to x)) }=
               (from (to x))                ={ fromTo x              }=
               x                            QED)

isoSym : Iso a b -> Iso b a
isoSym (MkIso to from toFrom fromTo) = MkIso from to fromTo toFrom

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


eitherCong : Iso a a' -> Iso b b' -> Iso (Either a b) (Either a' b')
eitherCong {a = a} {a' = a'} {b = b} {b' = b'}
           (MkIso to from toFrom fromTo)
           (MkIso to' from' toFrom' fromTo') =
  MkIso (eitherMap to to') (eitherMap from from') ok1 ok2
    where eitherMap : (c -> c') -> (d -> d') -> Either c d -> Either c' d'
          eitherMap f g (Left x)  = Left (f x)
          eitherMap f g (Right x) = Right (g x)
          ok1 : (x : Either a' b') -> eitherMap to to' (eitherMap from from' x) = x
          ok1 (Left x)  = cong (toFrom x)
          ok1 (Right x) = cong (toFrom' x)
          ok2 : (x : Either a b) -> eitherMap from from' (eitherMap to to' x) = x
          ok2 (Left x)  = cong (fromTo x)
          ok2 (Right x) = cong (fromTo' x)

eitherCongLeft : Iso a a' -> Iso (Either a b) (Either a' b)
eitherCongLeft i = eitherCong i isoRefl

eitherCongRight : Iso b b' -> Iso (Either a b) (Either a b')
eitherCongRight i = eitherCong isoRefl i

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

pairCong : Iso a a' -> Iso b b' -> Iso (a, b) (a', b')
pairCong {a = a} {a' = a'} {b = b} {b' = b'}
         (MkIso to from toFrom fromTo)
         (MkIso to' from' toFrom' fromTo') =
  MkIso to'' from'' iso1 iso2
    where to'' : (a, b) -> (a', b')
          to'' (x, y) = (to x, to' y)
          from'' : (a', b') -> (a, b)
          from'' (x, y) = (from x, from' y)
          iso1 : (x : (a', b')) -> to'' (from'' x) = x
          iso1 (x, y) = rewrite toFrom x in
                        rewrite toFrom' y in
                        refl
          iso2 : (x : (a, b)) -> from'' (to'' x) = x
          iso2 (x, y) = rewrite fromTo x in
                        rewrite fromTo' y in
                        refl

pairCongLeft : Iso a a' -> Iso (a, b) (a', b)
pairCongLeft i = pairCong i isoRefl

pairCongRight : Iso b b' -> Iso (a, b) (a, b')
pairCongRight = pairCong isoRefl

-- Distributivity of products over sums
distribLeft : Iso (Either a b, c) (Either (a, c) (b, c))
distribLeft = MkIso to from toFrom fromTo
  where to : (Either a b, c) -> Either (a, c) (b, c)
        to (Left x, y) = Left (x, y)
        to (Right x, y) = Right (x, y)
        from : Either (a, c) (b, c) -> (Either a b, c)
        from (Left (x, y)) = (Left x, y)
        from (Right (x, y)) = (Right x, y)
        toFrom : (x : Either (a, c) (b, c)) -> to (from x) = x
        toFrom (Left (x, y)) = refl
        toFrom (Right (x, y)) = refl
        fromTo : (x : (Either a b, c)) -> from (to x) = x
        fromTo (Left x, y) = refl
        fromTo (Right x, y) = refl

distribRight : Iso (a, Either b c) (Either (a, b) (a, c))
distribRight {a} {b} {c} = (pairComm `isoTrans` distribLeft) `isoTrans` eitherCong pairComm pairComm


-- Enable preorder reasoning syntax over isomorphisms
qed : (a : Type) -> Iso a a
qed a = isoRefl

step : (a : Type) -> Iso a b -> Iso b c -> Iso a c
step a iso1 iso2 = isoTrans iso1 iso2



-- Isomorphisms over Maybe
maybeCong : Iso a b -> Iso (Maybe a) (Maybe b)
maybeCong {a} {b} (MkIso to from toFrom fromTo) = MkIso (map to) (map from) ok1 ok2
  where ok1 : (y : Maybe b) -> map to (map from y) = y
        ok1 Nothing = refl
        ok1 (Just x) = (Just (to (from x))) ={ cong (toFrom x) }= (Just x) QED
        ok2 : (x : Maybe a) -> map from (map to x) = x
        ok2 Nothing = refl
        ok2 (Just x) = (Just (from (to x))) ={ cong (fromTo x) }= (Just x) QED

maybeEither : Iso (Maybe a) (Either a ())
maybeEither = MkIso to from iso1 iso2
  where to : Maybe a -> Either a ()
        to Nothing  = Right ()
        to (Just x) = Left x
        from : Either a () -> Maybe a
        from (Left x)   = Just x
        from (Right ()) = Nothing
        iso1 : (x : Either a ()) -> to (from x) = x
        iso1 (Left x) = refl
        iso1 (Right ()) = refl
        iso2 : (y : Maybe a) -> from (to y) = y
        iso2 Nothing = refl
        iso2 (Just x) = refl

maybeVoidUnit : Iso (Maybe _|_) ()
maybeVoidUnit = (Maybe _|_)     ={ maybeEither   }=
                (Either _|_ ()) ={ eitherBotLeft }=
                ()              QED

eitherMaybeLeftMaybe : Iso (Either (Maybe a) b) (Maybe (Either a b))
eitherMaybeLeftMaybe {a} {b} =
  (Either (Maybe a) b)     ={ eitherCongLeft maybeEither }=
  (Either (Either a ()) b) ={ eitherAssoc                }=
  (Either a (Either () b)) ={ eitherCongRight eitherComm }=
  (Either a (Either b ())) ={ isoSym eitherAssoc         }=
  (Either (Either a b) ()) ={ isoSym maybeEither         }=
  (Maybe (Either a b))     QED


eitherMaybeRightMaybe : Iso (Either a (Maybe b)) (Maybe (Either a b))
eitherMaybeRightMaybe {a} {b} =
  (Either a (Maybe b)) ={ eitherComm           }=
  (Either (Maybe b) a) ={ eitherMaybeLeftMaybe }=
  (Maybe (Either b a)) ={ maybeCong eitherComm }=
  (Maybe (Either a b)) QED


-- Isomorphisms over Fin

maybeIsoS : Iso (Maybe (Fin n)) (Fin (S n))
maybeIsoS = MkIso forth back fb bf
  where forth : Maybe (Fin n) -> Fin (S n)
        forth Nothing = fZ
        forth (Just x) = fS x
        back : Fin (S n) -> Maybe (Fin n)
        back fZ = Nothing
        back (fS x) = Just x
        bf : (x : Maybe (Fin n)) -> back (forth x) = x
        bf Nothing = refl
        bf (Just x) = refl
        fb : (y : Fin (S n)) -> forth (back y) = y
        fb fZ = refl
        fb (fS x) = refl

finZeroBot : Iso (Fin 0) _|_
finZeroBot = MkIso (\x => FalseElim (uninhabited x))
                   (\x => FalseElim x)
                   (\x => FalseElim x)
                   (\x => FalseElim (uninhabited x))

eitherFinPlus : Iso (Either (Fin m) (Fin n)) (Fin (m + n))
eitherFinPlus {m = Z} {n=n} =
  (Either (Fin 0) (Fin n)) ={ eitherCongLeft finZeroBot }=
  (Either _|_ (Fin n))     ={ eitherBotLeft             }=
  (Fin n)                  QED
eitherFinPlus {m = S k} {n=n} =
  (Either (Fin (S k)) (Fin n))     ={ eitherCongLeft (isoSym maybeIsoS) }=
  (Either (Maybe (Fin k)) (Fin n)) ={ eitherMaybeLeftMaybe              }=
  (Maybe (Either (Fin k) (Fin n))) ={ maybeCong eitherFinPlus           }=
  (Maybe (Fin (k + n)))            ={ maybeIsoS                         }=
  (Fin (S (k + n)))                QED


finPairTimes : Iso (Fin m, Fin n) (Fin (m * n))
finPairTimes {m = Z} {n=n} =
  (Fin Z, Fin n) ={ pairCongLeft finZeroBot }=
  (_|_, Fin n)   ={ pairBotLeft             }=
  _|_            ={ isoSym finZeroBot       }=
  (Fin Z)        QED
finPairTimes {m = S k} {n=n} =
  (Fin (S k), Fin n)                  ={ pairCongLeft (isoSym maybeIsoS)      }=
  (Maybe (Fin k), Fin n)              ={ pairCongLeft maybeEither             }=
  (Either (Fin k) (), Fin n)          ={ distribLeft                          }=
  (Either (Fin k, Fin n) ((), Fin n)) ={ eitherCong finPairTimes pairUnitLeft }=
  (Either (Fin (k * n)) (Fin n))      ={ eitherComm                           }=
  (Either (Fin n) (Fin (k * n)))      ={ eitherFinPlus                        }=
  (Fin (n + (k * n)))                 QED

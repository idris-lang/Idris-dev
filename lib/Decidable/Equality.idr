module Decidable.Equality

import Builtins

--------------------------------------------------------------------------------
-- Utility lemmas
--------------------------------------------------------------------------------

total negEqSym : {a : t} -> {b : t} -> (a = b -> _|_) -> (b = a -> _|_)
negEqSym p h = p (sym h)


--------------------------------------------------------------------------------
-- Decidable equality
--------------------------------------------------------------------------------

class DecEq t where
  total decEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)

--------------------------------------------------------------------------------
--- Unit
--------------------------------------------------------------------------------

instance DecEq () where
  decEq () () = Yes refl

--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------

total trueNotFalse : True = False -> _|_
trueNotFalse refl impossible

instance DecEq Bool where
  decEq True  True  = Yes refl
  decEq False False = Yes refl
  decEq True  False = No trueNotFalse
  decEq False True  = No (negEqSym trueNotFalse)

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

total OnotS : O = S n -> _|_
OnotS refl impossible

instance DecEq Nat where
  decEq O     O     = Yes refl
  decEq O     (S _) = No OnotS
  decEq (S _) O     = No (negEqSym OnotS)
  decEq (S n) (S m) with (decEq n m)
    | Yes p = Yes $ cong p
    | No p = No $ \h : (S n = S m) => p $ succInjective n m h

--------------------------------------------------------------------------------
-- Maybe
--------------------------------------------------------------------------------

total nothingNotJust : {x : t} -> (Nothing {a = t} = Just x) -> _|_
nothingNotJust refl impossible

instance (DecEq t) => DecEq (Maybe t) where
  decEq Nothing Nothing = Yes refl
  decEq (Just x') (Just y') with (decEq x' y')
    | Yes p = Yes $ cong p
    | No p = No $ \h : Just x' = Just y' => p $ justInjective h
  decEq Nothing (Just _) = No nothingNotJust
  decEq (Just _) Nothing = No (negEqSym nothingNotJust)

--------------------------------------------------------------------------------
-- Either
--------------------------------------------------------------------------------

total leftNotRight : {x : a} -> {y : b} -> Left {b = b} x = Right {a = a} y -> _|_
leftNotRight refl impossible

instance (DecEq a, DecEq b) => DecEq (Either a b) where
  decEq {b = b} (Left x') (Left y') with (decEq x' y')
    | Yes p = Yes $ cong p
    | No p = No $ \h : Left x' = Left y' => p $ leftInjective {b = b} h
  decEq (Right x') (Right y') with (decEq x' y')
    | Yes p = Yes $ cong p
    | No p = No $ \h : Right x' = Right y' => p $ rightInjective {a = a} h
  decEq (Left x') (Right y') = No leftNotRight
  decEq (Right x') (Left y') = No $ negEqSym leftNotRight

--------------------------------------------------------------------------------
-- Fin
--------------------------------------------------------------------------------

total fONotfS : {f : Fin n} -> fO {k = n} = fS f -> _|_
fONotfS refl impossible

instance DecEq (Fin n) where
  decEq fO fO = Yes refl
  decEq fO (fS f) = No fONotfS
  decEq (fS f) fO = No $ negEqSym fONotfS
  decEq (fS f) (fS f') with (decEq f f')
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ fSinjective {f = f} {f' = f'} h



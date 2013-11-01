module Decidable.Equality

import Prelude

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

total OnotS : Z = S n -> _|_
OnotS refl impossible

instance DecEq Nat where
  decEq Z     Z     = Yes refl
  decEq Z     (S _) = No OnotS
  decEq (S _) Z     = No (negEqSym OnotS)
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
  decEq (Left x') (Left y') with (decEq x' y')
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

total fZNotfS : {f : Fin n} -> fZ {k = n} = fS f -> _|_
fZNotfS refl impossible

instance DecEq (Fin n) where
  decEq fZ fZ = Yes refl
  decEq fZ (fS f) = No fZNotfS
  decEq (fS f) fZ = No $ negEqSym fZNotfS
  decEq (fS f) (fS f') with (decEq f f')
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ fSinjective {f = f} {f' = f'} h

--------------------------------------------------------------------------------
-- Tuple
--------------------------------------------------------------------------------

lemma_both_neq : {x : a, y : b, x' : c, y' : d} -> (x = x' -> _|_) -> (y = y' -> _|_) -> ((x, y) = (x', y') -> _|_)
lemma_both_neq p_x_not_x' p_y_not_y' refl = p_x_not_x' refl

lemma_snd_neq : {x : a, y : b, y' : d} -> (x = x) -> (y = y' -> _|_) -> ((x, y) = (x, y') -> _|_)
lemma_snd_neq refl p refl = p refl

lemma_fst_neq_snd_eq : {x : a, x' : b, y : c, y' : d} ->
                       (x = x' -> _|_) ->
                       (y = y') ->
                       ((x, y) = (x', y) -> _|_)
lemma_fst_neq_snd_eq p_x_not_x' refl refl = p_x_not_x' refl

instance (DecEq a, DecEq b) => DecEq (a, b) where
  decEq (a, b) (a', b') with (decEq a a')
    decEq (a, b) (a, b') | (Yes refl) with (decEq b b')
      decEq (a, b) (a, b) | (Yes refl) | (Yes refl) = Yes refl
      decEq (a, b) (a, b') | (Yes refl) | (No p) = No (\eq => lemma_snd_neq refl p eq)
    decEq (a, b) (a', b') | (No p) with (decEq b b')
      decEq (a, b) (a', b) | (No p) | (Yes refl) =  No (\eq => lemma_fst_neq_snd_eq p refl eq)
      decEq (a, b) (a', b') | (No p) | (No p') = No (\eq => lemma_both_neq p p' eq)


--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

lemma_val_not_nil : {x : t, xs : List t} -> ((x :: xs) = Prelude.List.Nil {a = t} -> _|_)
lemma_val_not_nil refl impossible

lemma_x_eq_xs_neq : {x : t, xs : List t, y : t, ys : List t} -> (x = y) -> (xs = ys -> _|_) -> ((x :: xs) = (y :: ys) -> _|_)
lemma_x_eq_xs_neq refl p refl = p refl

lemma_x_neq_xs_eq : {x : t, xs : List t, y : t, ys : List t} -> (x = y -> _|_) -> (xs = ys) -> ((x :: xs) = (y :: ys) -> _|_)
lemma_x_neq_xs_eq p refl refl = p refl

lemma_x_neq_xs_neq : {x : t, xs : List t, y : t, ys : List t} -> (x = y -> _|_) -> (xs = ys -> _|_) -> ((x :: xs) = (y :: ys) -> _|_)
lemma_x_neq_xs_neq p p' refl = p refl

instance DecEq a => DecEq (List a) where
  decEq [] [] = Yes refl
  decEq (x :: xs) [] = No lemma_val_not_nil
  decEq [] (x :: xs) = No (negEqSym lemma_val_not_nil)
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (x :: ys) | Yes refl with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | (Yes refl) | (Yes refl) = Yes refl -- maybe another yes refl
      decEq (x :: xs) (x :: ys) | (Yes refl) | (No p) = No (\eq => lemma_x_eq_xs_neq refl p eq)
    decEq (x :: xs) (y :: ys) | No p with (decEq xs ys)
      decEq (x :: xs) (y :: xs) | (No p) | (Yes refl) = No (\eq => lemma_x_neq_xs_eq p refl eq)
      decEq (x :: xs) (y :: ys) | (No p) | (No p') = No (\eq => lemma_x_neq_xs_neq p p' eq)


--------------------------------------------------------------------------------
-- Vect
--------------------------------------------------------------------------------

total
vectInjective1 : {xs, ys : Vect n a} -> {x, y : a} -> x :: xs = y :: ys -> x = y
vectInjective1 {x=x} {y=x} {xs=xs} {ys=xs} refl = refl

total
vectInjective2 : {xs, ys : Vect n a} -> {x, y : a} -> x :: xs = y :: ys -> xs = ys
vectInjective2 {x=x} {y=x} {xs=xs} {ys=xs} refl = refl

instance DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes refl
  decEq (x :: xs) (y :: ys) with (decEq x y, decEq xs ys)
    decEq (x :: xs) (x :: xs) | (Yes refl, Yes refl) = Yes refl
    decEq (x :: xs) (y :: ys) | (_, No nEqTl) = No (\p => nEqTl (vectInjective2 p))
    decEq (x :: xs) (y :: ys) | (No nEqHd, _) = No (\p => nEqHd (vectInjective1 p))

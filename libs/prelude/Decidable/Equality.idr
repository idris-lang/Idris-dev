module Decidable.Equality

import Builtins
import Prelude.Basics
import Prelude.Bool
import Prelude.Interfaces
import Prelude.Either
import Prelude.List
import Prelude.Nat
import Prelude.Maybe

%access public export

--------------------------------------------------------------------------------
-- Utility lemmas
--------------------------------------------------------------------------------

||| The negation of equality is symmetric (follows from symmetry of equality)
total negEqSym : {a : t} -> {b : t} -> (a = b -> Void) -> (b = a -> Void)
negEqSym p h = p (sym h)


--------------------------------------------------------------------------------
-- Decidable equality
--------------------------------------------------------------------------------

||| Decision procedures for propositional equality
interface DecEq t where
  ||| Decide whether two elements of `t` are propositionally equal
  total decEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)

--------------------------------------------------------------------------------
--- Unit
--------------------------------------------------------------------------------

implementation DecEq () where
  decEq () () = Yes Refl

--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------
total trueNotFalse : True = False -> Void
trueNotFalse Refl impossible

implementation DecEq Bool where
  decEq True  True  = Yes Refl
  decEq False False = Yes Refl
  decEq True  False = No trueNotFalse
  decEq False True  = No (negEqSym trueNotFalse)

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

total ZnotS : Z = S n -> Void
ZnotS Refl impossible

implementation DecEq Nat where
  decEq Z     Z     = Yes Refl
  decEq Z     (S _) = No ZnotS
  decEq (S _) Z     = No (negEqSym ZnotS)
  decEq (S n) (S m) with (decEq n m)
    | Yes p = Yes $ cong p
    | No p = No $ \h : (S n = S m) => p $ succInjective n m h

--------------------------------------------------------------------------------
-- Maybe
--------------------------------------------------------------------------------

total nothingNotJust : {x : t} -> (Nothing {a = t} = Just x) -> Void
nothingNotJust Refl impossible

implementation (DecEq t) => DecEq (Maybe t) where
  decEq Nothing Nothing = Yes Refl
  decEq (Just x') (Just y') with (decEq x' y')
    | Yes p = Yes $ cong p
    | No p = No $ \h : Just x' = Just y' => p $ justInjective h
  decEq Nothing (Just _) = No nothingNotJust
  decEq (Just _) Nothing = No (negEqSym nothingNotJust)

--------------------------------------------------------------------------------
-- Either
--------------------------------------------------------------------------------

total leftNotRight : {x : a} -> {y : b} -> Left {b = b} x = Right {a = a} y -> Void
leftNotRight Refl impossible

implementation (DecEq a, DecEq b) => DecEq (Either a b) where
  decEq (Left x') (Left y') with (decEq x' y')
    | Yes p = Yes $ cong p
    | No p = No $ \h : Left x' = Left y' => p $ leftInjective {b = b} h
  decEq (Right x') (Right y') with (decEq x' y')
    | Yes p = Yes $ cong p
    | No p = No $ \h : Right x' = Right y' => p $ rightInjective {a = a} h
  decEq (Left x') (Right y') = No leftNotRight
  decEq (Right x') (Left y') = No $ negEqSym leftNotRight

--------------------------------------------------------------------------------
-- Tuple
--------------------------------------------------------------------------------

lemma_both_neq : {x : a, y : b, x' : c, y' : d} -> (x = x' -> Void) -> (y = y' -> Void) -> ((x, y) = (x', y') -> Void)
lemma_both_neq p_x_not_x' p_y_not_y' Refl = p_x_not_x' Refl

lemma_snd_neq : {x : a, y : b, y' : d} -> (x = x) -> (y = y' -> Void) -> ((x, y) = (x, y') -> Void)
lemma_snd_neq Refl p Refl = p Refl

lemma_fst_neq_snd_eq : {x : a, x' : b, y : c, y' : d} ->
                       (x = x' -> Void) ->
                       (y = y') ->
                       ((x, y) = (x', y) -> Void)
lemma_fst_neq_snd_eq p_x_not_x' Refl Refl = p_x_not_x' Refl

implementation (DecEq a, DecEq b) => DecEq (a, b) where
  decEq (a, b) (a', b')     with (decEq a a')
    decEq (a, b) (a, b')    | (Yes Refl) with (decEq b b')
      decEq (a, b) (a, b)   | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (a, b) (a, b')  | (Yes Refl) | (No p) = No (\eq => lemma_snd_neq Refl p eq)
    decEq (a, b) (a', b')   | (No p)     with (decEq b b')
      decEq (a, b) (a', b)  | (No p)     | (Yes Refl) =  No (\eq => lemma_fst_neq_snd_eq p Refl eq)
      decEq (a, b) (a', b') | (No p)     | (No p') = No (\eq => lemma_both_neq p p' eq)


--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

lemma_val_not_nil : {x : t, xs : List t} -> ((x :: xs) = Prelude.List.Nil {elem = t} -> Void)
lemma_val_not_nil Refl impossible

lemma_x_eq_xs_neq : {x : t, xs : List t, y : t, ys : List t} -> (x = y) -> (xs = ys -> Void) -> ((x :: xs) = (y :: ys) -> Void)
lemma_x_eq_xs_neq Refl p Refl = p Refl

lemma_x_neq_xs_eq : {x : t, xs : List t, y : t, ys : List t} -> (x = y -> Void) -> (xs = ys) -> ((x :: xs) = (y :: ys) -> Void)
lemma_x_neq_xs_eq p Refl Refl = p Refl

lemma_x_neq_xs_neq : {x : t, xs : List t, y : t, ys : List t} -> (x = y -> Void) -> (xs = ys -> Void) -> ((x :: xs) = (y :: ys) -> Void)
lemma_x_neq_xs_neq p p' Refl = p Refl

implementation DecEq a => DecEq (List a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) [] = No lemma_val_not_nil
  decEq [] (x :: xs) = No (negEqSym lemma_val_not_nil)
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (x :: ys) | Yes Refl with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (x :: xs) (x :: ys) | (Yes Refl) | (No p) = No (\eq => lemma_x_eq_xs_neq Refl p eq)
    decEq (x :: xs) (y :: ys) | No p with (decEq xs ys)
      decEq (x :: xs) (y :: xs) | (No p) | (Yes Refl) = No (\eq => lemma_x_neq_xs_eq p Refl eq)
      decEq (x :: xs) (y :: ys) | (No p) | (No p') = No (\eq => lemma_x_neq_xs_neq p p' eq)


-- For the primitives, we have to cheat because we don't have access to their
-- internal implementations.

--------------------------------------------------------------------------------
-- Int
--------------------------------------------------------------------------------

implementation DecEq Int where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq 
                     False => No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = really_believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void

--------------------------------------------------------------------------------
-- Char
--------------------------------------------------------------------------------

implementation DecEq Char where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq 
                     False => No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = really_believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void

--------------------------------------------------------------------------------
-- Integer
--------------------------------------------------------------------------------

implementation DecEq Integer where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq 
                     False => No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = really_believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void

--------------------------------------------------------------------------------
-- String
--------------------------------------------------------------------------------

implementation DecEq String where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq 
                     False => No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = really_believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void

--------------------------------------------------------------------------------
-- Ptr
--------------------------------------------------------------------------------

implementation DecEq Ptr where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq 
                     False => No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = really_believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void

--------------------------------------------------------------------------------
-- ManagedPtr
--------------------------------------------------------------------------------

implementation DecEq ManagedPtr where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq 
                     False => No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = really_believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void

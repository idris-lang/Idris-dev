module elem

import Decidable.Equality
import Data.Vect

using (xs : List a)
  data Elem  : a -> List a -> Type where
       Here  : Elem x (x :: xs)
       There : Elem x xs -> Elem x (y :: xs)

isElem : (x : Nat) -> (xs : List Nat) -> Maybe (Elem x xs)
isElem x xs = ?isElem_rhs

vadd : Num a => Vect n a -> Vect n a -> Vect n a
vadd xs ys = localZipWith (+) xs ys where
   localZipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
   localZipWith f [] [] = []
   localZipWith f (_ :: _) ys = ?localZipWith_rhs

map : (a -> b) -> Vect n a -> Vect n b
map f [] = []
map f (x :: xs) = ?maprhs

isElem2 : (x : Nat) -> (xs : List Nat) -> Maybe (Elem x xs)
isElem2 x [] = Nothing
isElem2 x (y :: ys) = ?isElem_rhs_2

isElem3 : (x : Nat) -> (xs : List Nat) -> Maybe (Elem x xs)
isElem3 x [] = Nothing
isElem3 x (y :: ys) with (decEq x y)
  isElem3 x (y :: ys) | (Yes p) = ?isElem3_rhs_1
  isElem3 x (y :: ys) | (No _) = ?isElem3_rhs_2

foo : List a -> List a
foo xs = case xs of
              xs' => ?bar

elemVoid1 : elem.Elem x [] -> Void
elemVoid1 x = ?elemVoid1_rhs

elemVoid2 : elem.Elem x [] -> Void
elemVoid2 x = case x of
                   case_val => ?elemVoid2_rhs



module Data.Vect

import Language.Reflection

--------------------------------------------------------------------------------
-- Elem
--------------------------------------------------------------------------------

data Elem : a -> Vect a k -> Type where
  Here : {xs : Vect a k} -> Elem x (x::xs)
  There : {xs : Vect a k} -> Elem x xs -> Elem x (y::xs)

findElem : Nat -> List (TTName, Binder TT) -> TT -> Tactic
findElem O ctxt goal = Refine "Here" `Seq` Solve
findElem (S n) ctxt goal = GoalType "Elem" (Try (Refine "Here" `Seq` Solve) (Refine "There" `Seq` (Solve `Seq` findElem n ctxt goal)))

replaceElem : (xs : Vect t k) -> Elem x xs -> (y : t) -> (ys : Vect t k ** Elem y ys)
replaceElem (x::xs) Here y = (y :: xs ** Here)
replaceElem (x::xs) (There xinxs) y with (replaceElem xs xinxs y)
  | (ys ** yinys) = (x :: ys ** There yinys)

replaceByElem : (xs : Vect t k) -> Elem x xs -> t -> Vect t k
replaceByElem (x::xs) Here y = y :: xs
replaceByElem (x::xs) (There xinxs) y = x :: replaceByElem xs xinxs y

mapElem : {xs : Vect t k} -> {f : t -> u} -> Elem x xs -> Elem (f x) (map f xs)
mapElem Here = Here
mapElem (There e) = There (mapElem e)


module Data.Vect

import Language.Reflection

%access public
%default total

--------------------------------------------------------------------------------
-- Elem
--------------------------------------------------------------------------------

using (xs : Vect k a)
  ||| A proof that some element is found in a vector
  data Elem : a -> Vect k a -> Type where
    Here : Elem x (x::xs)
    There : Elem x xs -> Elem x (y::xs)

||| Nothing can be in an empty Vect
noEmptyElem : {x : a} -> Elem x [] -> _|_
noEmptyElem Here impossible

||| An item not in the head and not in the tail is not in the Vect at all
neitherHereNorThere : {x, y : a} -> {xs : Vect n a} -> Not (x = y) -> Not (Elem x xs) -> Not (Elem x (y :: xs))
neitherHereNorThere xneqy xninxs Here = xneqy refl
neitherHereNorThere xneqy xninxs (There xinxs) = xninxs xinxs

||| A decision procedure for Elem
isElem : DecEq a => (x : a) -> (xs : Vect n a) -> Dec (Elem x xs)
isElem x [] = No noEmptyElem
isElem x (y :: xs) with (decEq x y)
  isElem x (x :: xs) | (Yes refl) = Yes Here
  isElem x (y :: xs) | (No xneqy) with (isElem x xs)
    isElem x (y :: xs) | (No xneqy) | (Yes xinxs) = Yes (There xinxs)
    isElem x (y :: xs) | (No xneqy) | (No xninxs) = No (neitherHereNorThere xneqy xninxs)

||| A tactic for discovering where, if anywhere, an element is in a vector
||| @ n how many elements to search before giving up
findElem : (n : Nat) -> List (TTName, Binder TT) -> TT -> Tactic
findElem Z ctxt goal = Refine "Here" `Seq` Solve
findElem (S n) ctxt goal = GoalType "Elem" (Try (Refine "Here" `Seq` Solve) (Refine "There" `Seq` (Solve `Seq` findElem n ctxt goal)))

replaceElem : (xs : Vect k t) -> Elem x xs -> (y : t) -> (ys : Vect k t ** Elem y ys)
replaceElem (x::xs) Here y = (y :: xs ** Here)
replaceElem (x::xs) (There xinxs) y with (replaceElem xs xinxs y)
  | (ys ** yinys) = (x :: ys ** There yinys)

replaceByElem : (xs : Vect k t) -> Elem x xs -> t -> Vect k t
replaceByElem (x::xs) Here y = y :: xs
replaceByElem (x::xs) (There xinxs) y = x :: replaceByElem xs xinxs y

mapElem : {xs : Vect k t} -> {f : t -> u} -> Elem x xs -> Elem (f x) (map f xs)
mapElem Here = Here
mapElem (There e) = There (mapElem e)


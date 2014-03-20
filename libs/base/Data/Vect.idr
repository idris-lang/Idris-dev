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


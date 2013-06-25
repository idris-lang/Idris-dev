module Data.HVect

import Data.Vect

%access public
%default total

using (k : Nat, ts : Vect Type k)
  data HVect : Vect Type k -> Type where
    Nil : HVect []
    (::) : t -> HVect ts -> HVect (t::ts)

  index : (i : Fin k) -> HVect ts -> index i ts
  index fO (x::xs) = x
  index (fS j) (x::xs) = index j xs

  deleteAt : {us : Vect Type (S l)} -> (i : Fin (S l)) -> HVect us -> HVect (deleteAt i us)
  deleteAt fO (x::xs) = xs
  deleteAt {l = S m} (fS j) (x::xs) = x :: deleteAt j xs
  deleteAt _ [] impossible

  replaceAt : (i : Fin k) -> t -> HVect ts -> HVect (replaceAt i t ts)
  replaceAt fO y (x::xs) = y::xs
  replaceAt (fS j) y (x::xs) = x :: replaceAt j y xs

  updateAt : (i : Fin k) -> (index i ts -> t) -> HVect ts -> HVect (replaceAt i t ts)
  updateAt fO f (x::xs) = f x :: xs
  updateAt (fS j) f (x::xs) = x :: updateAt j f xs

  (++) : {us : Vect Type l} -> HVect ts -> HVect us -> HVect (ts ++ us)
  (++) [] ys = ys
  (++) (x::xs) ys = x :: (xs ++ ys)

  instance Eq (HVect []) where
    [] == [] = True

  instance (Eq t, Eq (HVect ts)) => Eq (HVect (t::ts)) where
    (x::xs) == (y::ys) = x == y && xs == ys

  class Shows (k : Nat) (ts : Vect Type k) where
    shows : HVect ts -> Vect String k

  instance Shows O [] where
    shows [] = []

  instance (Show t, Shows k ts) => Shows (S k) (t::ts) where
    shows (x::xs) = show x :: shows xs

  instance (Shows k ts) => Show (HVect ts) where
    show xs = show (shows xs)

  get : {default tactics { applyTactic findElem 100; solve; } p : Elem t ts} -> HVect ts -> t
  get {p = Here} (x::xs) = x
  get {p = There p'} (x::xs) = get {p = p'} xs

  put : {default tactics { applyTactic findElem 100; solve; } p : Elem t ts} -> t -> HVect ts -> HVect ts
  put {p = Here} y (x::xs) = y :: xs
  put {p = There p'} y (x::xs) = x :: put {p = p'} y xs

  update : {default tactics { applyTactic findElem 100; solve; } p : Elem t ts} -> (t -> u) -> HVect ts -> HVect (replaceByElem ts p u)
  update {p = Here} f (x::xs) = f x :: xs
  update {p = There p'} f (x::xs) = x :: update {p = p'} f xs


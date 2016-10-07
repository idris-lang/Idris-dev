module Data.HVect

import public Data.Vect

%access public export
%default total

||| Heterogeneous vectors where the type index gives, element-wise,
||| the types of the contents.
data HVect : Vect k Type -> Type where
  Nil : HVect []
  (::) : t -> HVect ts -> HVect (t::ts)

||| Extract an element from an HVect
index : (i : Fin k) -> HVect ts -> index i ts
index FZ (x::xs) = x
index (FS j) (x::xs) = index j xs

deleteAt : (i : Fin (S l)) -> HVect us -> HVect (deleteAt i us)
deleteAt FZ (x::xs) = xs
deleteAt {l = S m} (FS j) (x::xs) = x :: deleteAt j xs
deleteAt {l = Z}   (FS j) (x::xs) = absurd j
deleteAt _ [] impossible

replaceAt : (i : Fin k) -> t -> HVect ts -> HVect (replaceAt i t ts)
replaceAt FZ y (x::xs) = y::xs
replaceAt (FS j) y (x::xs) = x :: replaceAt j y xs

updateAt : (i : Fin k) -> (index i ts -> t) -> HVect ts -> HVect (replaceAt i t ts)
updateAt FZ f (x::xs) = f x :: xs
updateAt (FS j) f (x::xs) = x :: updateAt j f xs

||| Append two `HVect`s.
(++) : HVect ts -> HVect us -> HVect (ts ++ us)
(++) [] ys = ys
(++) (x::xs) ys = x :: (xs ++ ys)

implementation Eq (HVect []) where
  [] == [] = True

implementation (Eq t, Eq (HVect ts)) => Eq (HVect (t::ts)) where
  (x::xs) == (y::ys) = x == y && xs == ys

total
hvectInjective1 : {xs, ys: HVect ts} -> {x, y:a} -> x :: xs = y :: ys -> x = y
hvectInjective1 Refl = Refl

total
hvectInjective2 : {xs, ys: HVect ts} -> {x, y:a} -> x :: xs = y :: ys -> xs = ys
hvectInjective2 Refl = Refl

implementation DecEq (HVect []) where
  decEq [] [] = Yes Refl

implementation (DecEq t, DecEq (HVect ts)) => DecEq (HVect (t::ts)) where
  decEq (x::xs) (y::ys) with (decEq x y)
    decEq (z::xs) (z::ys) | Yes Refl with (decEq xs ys)
      decEq (z::zs) (z::zs) | Yes Refl | Yes Refl = Yes Refl
      decEq (z::xs) (z::ys) | Yes Refl | No ctr = No (ctr . hvectInjective2)
    decEq (x::xs) (y::ys) | No ctr = No (ctr . hvectInjective1)

interface Shows (ts : Vect k Type) where
  shows : HVect ts -> Vect k String

implementation Shows [] where
  shows [] = []

implementation (Show t, Shows ts) => Shows (t::ts) where
  shows (x::xs) = show x :: shows xs

implementation (Shows ts) => Show (HVect ts) where
  show xs = "[" ++ (pack . intercalate [','] . map unpack . toList $ shows xs) ++ "]"

||| Extract an arbitrary element of the correct type.
||| @ t the goal type
get : HVect ts -> {auto p : Elem t ts} -> t
get (x :: xs) {p = Here} = x
get (x :: xs) {p = There p'} = get {p = p'} xs

||| Replace an element with the correct type.
put : t -> HVect ts -> {auto p : Elem t ts} -> HVect ts
put y (x::xs) {p = Here} = y :: xs
put y (x::xs) {p = There p'} = x :: put {p = p'} y xs

||| Update an element with the correct type.
update : (t -> u) -> HVect ts -> {auto p : Elem t ts} -> HVect (replaceByElem ts p u)
update f (x::xs) {p = Here} = f x :: xs
update f (x::xs) {p = There p'} = x :: update {p = p'} f xs


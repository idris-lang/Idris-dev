module Data.Vect.Quantifiers

import Data.Vect

%access public export

||| A proof that some element of a vector satisfies some property
|||
||| @ P the property to be satsified
data Any : (P : a -> Type) -> Vect n a -> Type where
  ||| A proof that the satisfying element is the first one in the `Vect`
  Here  : {P : a -> Type} -> {xs : Vect n a} -> P x -> Any P (x :: xs)
  ||| A proof that the satsifying element is in the tail of the `Vect`
  There : {P : a -> Type} -> {xs : Vect n a} -> Any P xs -> Any P (x :: xs)

||| No element of an empty vector satisfies any property
anyNilAbsurd : {P : a -> Type} -> Any P Nil -> Void
anyNilAbsurd (Here _) impossible
anyNilAbsurd (There _) impossible

implementation Uninhabited (Any p Nil) where
  uninhabited = anyNilAbsurd

||| Eliminator for `Any`
anyElim : {xs : Vect n a} -> {P : a -> Type} -> (Any P xs -> b) -> (P x -> b) -> Any P (x :: xs) -> b
anyElim _ f (Here p) = f p
anyElim f _ (There p) = f p

||| Given a decision procedure for a property, determine if an element of a
||| vector satisfies it.
|||
||| @ P the property to be satisfied
||| @ dec the decision procedure
||| @ xs the vector to examine
any : {P : a -> Type} -> (dec : (x : a) -> Dec (P x)) -> (xs : Vect n a) -> Dec (Any P xs)
any _ Nil = No anyNilAbsurd
any p (x::xs) with (p x)
  | Yes prf = Yes (Here prf)
  | No prf =
    case any p xs of
      Yes prf' => Yes (There prf')
      No prf' => No (anyElim prf' prf)

||| A proof that all elements of a vector satisfy a property. It is a list of
||| proofs, corresponding element-wise to the `Vect`.
data All : (P : a -> Type) -> Vect n a -> Type where
  Nil : {P : a -> Type} -> All P Nil
  (::) : {P : a -> Type} -> {xs : Vect n a} -> P x -> All P xs -> All P (x :: xs)

||| If there does not exist an element that satifies the property, then it is
||| the case that all elements do not satisfy.
negAnyAll : {P : a -> Type} -> {xs : Vect n a} -> Not (Any P xs) -> All (\x => Not (P x)) xs
negAnyAll {xs=Nil} _ = Nil
negAnyAll {xs=(x::xs)} f = (\x => f (Here x)) :: negAnyAll (\x => f (There x))

notAllHere : {P : a -> Type} -> {xs : Vect n a} -> Not (P x) -> All P (x :: xs) -> Void
notAllHere _ Nil impossible
notAllHere np (p :: _) = np p

notAllThere : {P : a -> Type} -> {xs : Vect n a} -> Not (All P xs) -> All P (x :: xs) -> Void
notAllThere _ Nil impossible
notAllThere np (_ :: ps) = np ps

||| Given a decision procedure for a property, decide whether all elements of
||| a vector satisfy it.
|||
||| @ P the property
||| @ dec the decision procedure
||| @ xs the vector to examine
all : {P : a -> Type} -> (dec : (x : a) -> Dec (P x)) -> (xs : Vect n a) -> Dec (All P xs)
all _ Nil = Yes Nil
all d (x::xs) with (d x)
  | No prf = No (notAllHere prf)
  | Yes prf =
    case all d xs of
      Yes prf' => Yes (prf :: prf')
      No prf' => No (notAllThere prf')

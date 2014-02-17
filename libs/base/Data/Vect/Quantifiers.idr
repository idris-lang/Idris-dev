module Data.Vect.Quantifiers

data Any : (P : a -> Type) -> Vect n a -> Type where
  Here  : {P : a -> Type} -> {xs : Vect n a} -> P x -> Any P (x :: xs)
  There : {P : a -> Type} -> {xs : Vect n a} -> Any P xs -> Any P (x :: xs)

anyNilAbsurd : {P : a -> Type} -> Any P Nil -> _|_
anyNilAbsurd (Here _) impossible 
anyNilAbsurd (There _) impossible

anyElim : {xs : Vect n a} -> {P : a -> Type} -> (Any P xs -> b) -> (P x -> b) -> Any P (x :: xs) -> b
anyElim _ f (Here p) = f p
anyElim f _ (There p) = f p

any : {P : a -> Type} -> ((x : a) -> Dec (P x)) -> (xs : Vect n a) -> Dec (Any P xs)
any _ Nil = No anyNilAbsurd
any {P} p (x::xs) with (p x)
  | Yes prf = Yes (Here prf)
  | No prf =
    case any {P} p xs of
      Yes prf' => Yes (There prf')
      No prf' => No (anyElim prf' prf)

data All : (P : a -> Type) -> Vect n a -> Type where
  Nil : {P : a -> Type} -> All P Nil
  (::) : {P : a -> Type} -> {xs : Vect n a} -> P x -> All P xs -> All P (x :: xs)

negAnyAll : {P : a -> Type} -> {xs : Vect n a} -> Not (Any P xs) -> All (\x => Not (P x)) xs
negAnyAll {xs=Nil} _ = Nil
negAnyAll {xs=(x::xs)} f = (\x => f (Here x)) :: negAnyAll (\x => f (There x))

notAllHere : {P : a -> Type} -> {xs : Vect n a} -> Not (P x) -> All P (x :: xs) -> _|_
notAllHere _ Nil impossible
notAllHere np (p :: _) = np p

notAllThere : {P : a -> Type} -> {xs : Vect n a} -> Not (All P xs) -> All P (x :: xs) -> _|_
notAllThere _ Nil impossible
notAllThere np (_ :: ps) = np ps

all : {P : a -> Type} -> ((x : a) -> Dec (P x)) -> (xs : Vect n a) -> Dec (All P xs)
all _ Nil = Yes Nil
all {P} d (x::xs) with (d x)
  | No prf = No (notAllHere prf)
  | Yes prf =
    case all {P} d xs of
      Yes prf' => Yes (prf :: prf')
      No prf' => No (notAllThere prf')

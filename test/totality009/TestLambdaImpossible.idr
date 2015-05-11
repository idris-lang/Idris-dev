module TestLambdaImpossible

%default total

eqBool : (x, y : Bool) -> Dec (x = y)
eqBool False False = Yes Refl
eqBool False True = No (\(Refl) impossible)
eqBool True False = No (\(Refl) impossible)
eqBool True True = Yes Refl

data Elem : {a : Type} -> a -> Prelude.List.List a -> Type where
  Here : {a : Type} -> {x : a} -> {xs : List a} -> Elem x (x :: xs)
  There : {a : Type} -> {x, y : a} -> {xs : List a} -> Elem x xs -> Elem x (y :: xs)

notHereNotThere : Not (x = y) -> Not (Elem x xs) -> Not (Elem x (y :: xs))
notHereNotThere notEq notElem Here = notEq Refl
notHereNotThere notEq notElem (There elem) = notElem elem

decElem : DecEq a => (x : a) -> (xs : List a) -> Dec (Elem x xs)
decElem x [] = No (\Here impossible)
decElem x (y :: xs) with (decEq x y)
  decElem x (x :: xs) | (Yes Refl) = Yes Here
  decElem x (y :: xs) | (No notHere) with (decElem x xs)
    decElem x (y :: xs) | (No notHere) | (Yes prf) = Yes (There prf)
    decElem x (y :: xs) | (No notHere) | (No notThere) = No $ notHereNotThere notHere notThere


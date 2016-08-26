module Data.List

%access public export

||| A proof that some element is found in a list.
|||
||| Example: `the (Elem "bar" ["foo", "bar", "baz"]) (tactics { search })`
data Elem : a -> List a -> Type where
     ||| A proof that the element is at the front of the list.
     |||
     ||| Example: `the (Elem "a" ["a", "b"]) Here`
     Here : Elem x (x :: xs)
     ||| A proof that the element is after the front of the list
     |||
     ||| Example: `the (Elem "b" ["a", "b"]) (There Here)`
     There : (later : Elem x xs) -> Elem x (y :: xs)

implementation Uninhabited (Elem {a} x []) where
     uninhabited Here impossible
     uninhabited (There p) impossible

||| Is the given element a member of the given list.
|||
||| @x The element to be tested.
||| @xs The list to be checked against
isElem : DecEq a => (x : a) -> (xs : List a) -> Dec (Elem x xs)
isElem x [] = No absurd
isElem x (y :: xs) with (decEq x y)
  isElem x (x :: xs) | (Yes Refl) = Yes Here
  isElem x (y :: xs) | (No contra) with (isElem x xs)
    isElem x (y :: xs) | (No contra) | (Yes prf) = Yes (There prf)
    isElem x (y :: xs) | (No contra) | (No f) = No (mkNo contra f)
      where
        mkNo : {xs' : List a} ->
               ((x' = y') -> Void) -> (Elem x' xs' -> Void) ->
               Elem x' (y' :: xs') -> Void
        mkNo f g Here = f Refl
        mkNo f g (There x) = g x

||| Remove the element at the given position.
|||
||| @xs The list to be removed from
||| @p A proof that the element to be removed is in the list
dropElem : (xs : List a) -> (p : Elem x xs) -> List a
dropElem (x :: ys) Here = ys
dropElem (x :: ys) (There p) = x :: dropElem ys p

||| The intersectBy function returns the intersect of two lists by user-supplied equality predicate.
intersectBy : (a -> a -> Bool) -> List a -> List a -> List a
intersectBy eq xs ys = [x | x <- xs, any (eq x) ys]

||| Compute the intersection of two lists according to their `Eq` implementation.
|||
||| ```idris example
||| intersect [1, 2, 3, 4] [2, 4, 6, 8]
||| ```
|||
intersect : (Eq a) => List a -> List a -> List a
intersect = intersectBy (==)

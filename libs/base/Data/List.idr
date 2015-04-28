module Data.List

%access public

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
     There : Elem x xs -> Elem x (y :: xs)

instance Uninhabited (Elem {a} x []) where
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

namespace ContainsKey

  ||| A proof that an associative list contains a pair with given key.
  data ContainsKey : List (k,v) -> k -> Type where
      ||| A proof that the pair containing the key is the head of the list.
      Here  : ContainsKey ((k,v)::ps) k
      ||| A proof that the pair containing the key is in the tail of the list.
      There : ContainsKey ps k -> ContainsKey ((k',v)::ps) k

  instance Uninhabited (ContainsKey [] k) where
        uninhabited Here impossible
        uninhabited (There p) impossible

  ||| Does the association list contain a pair with the given key?
  |||
  ||| @ps The list to be checked against
  ||| @k  The key to check for
  containsKey : DecEq 'k => (ps:List ('k,'v)) -> (k:'k) -> Dec (ps `ContainsKey` k)
  containsKey [] k = No absurd
  containsKey ((a, b) :: ps) k with (decEq a k)
    containsKey ((k, b) :: ps) k | (Yes Refl) = Yes Here
    containsKey ((a, b) :: ps) k | (No notHere) with (ps `containsKey` k)
      containsKey ((a, b) :: ps) k | (No notHere) | (Yes prf) = Yes (There prf)
      containsKey ((a, b) :: ps) k | (No notHere) | (No notThere) = No (mkNo notHere notThere)
        where
          mkNo : ((k' = k) -> Void) ->
                 (ps `ContainsKey` k -> Void) ->
                 ((k',v')::ps) `ContainsKey` k -> Void
          mkNo f g Here = f Refl
          mkNo f g (There x) = g x

||| The intersectBy function returns the intersect of two lists by user-supplied equality predicate.
intersectBy : (a -> a -> Bool) -> List a -> List a -> List a
intersectBy eq xs ys = [x | x <- xs, any (eq x) ys]

||| Compute the intersection of two lists according to their `Eq` instance.
|||
||| ```idris example
||| intersect [1, 2, 3, 4] [2, 4, 6, 8]
||| ```
|||
intersect : (Eq a) => List a -> List a -> List a
intersect = intersectBy (==)

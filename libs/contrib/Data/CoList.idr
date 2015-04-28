module Data.CoList

%access public

||| Idris will know that it always can produce a new element in finite time
codata CoList : Type -> Type where
  Nil : CoList a
  (::) : a -> CoList a -> CoList a

infixr 7 ++

||| Append two CoLists
(++) : CoList a -> CoList a -> CoList a
(++) []      right = right
(++) (x::xs) right = x :: (xs ++ right)

instance Semigroup (CoList a) where
  (<+>) = (++)

instance Monoid (CoList a) where
  neutral = []

instance Functor CoList where
  map f []      = []
  map f (x::xs) = f x :: map f xs

instance Show a => Show (CoList a) where
    show xs = "[" ++ show' "" xs ++ "]" where
        show' acc []        = acc
        show' acc [x]       = acc ++ show x
        show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs

||| Take the first `n` elements of `xs`
|||
||| If there are not enough elements, return the whole coList.
||| @ n how many elements to take
||| @ xs the coList to take them from
takeCo : (n : Nat) -> (xs : CoList a) -> List a
takeCo Z _ = []
takeCo (S n) [] = []
takeCo (S n) (x::xs) = x :: takeCo n xs

||| The unfoldr builds a list from a seed value. In some cases, unfoldr can undo a foldr operation.
|||
||| ``` idris example
||| unfoldr (\b => if b == 0 then Nothing else Just (b, b-1)) 10
||| ```
|||
unfoldr : (a -> Maybe (a, a)) -> a -> CoList a
unfoldr f x =
  case f x of
    Just (y, new_x) => y :: (unfoldr f new_x)
    _               => []

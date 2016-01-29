module Data.CoList

%access public export
%default total

||| Idris will know that it always can produce a new element in finite time
codata CoList : Type -> Type where
  Nil : CoList a
  (::) : a -> CoList a -> CoList a

||| Append two CoLists
(++) : CoList a -> CoList a -> CoList a
(++) []      right = right
(++) (x::xs) right = x :: (xs ++ right)

implementation Semigroup (CoList a) where
  (<+>) = (++)

implementation Monoid (CoList a) where
  neutral = []

implementation Functor CoList where
  map f []      = []
  map f (x::xs) = f x :: map f xs

implementation Show a => Show (CoList a) where
  show xs = "[" ++ show' "" 20 xs ++ "]" where
    show' : String -> (n : Nat) -> (xs : CoList a) -> String
    show' acc Z _             = acc ++ "..."
    show' acc (S n) []        = acc
    show' acc (S n) [x]       = acc ++ show x
    show' acc (S n) (x :: xs) = show' (acc ++ (show x) ++ ", ") n xs

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

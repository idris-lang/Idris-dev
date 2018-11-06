module Test

interface ListLike a where
  Elem : Type
  fromList : List Elem -> a

data Silly = None | Cons Int Silly

ListLike Silly where
  Elem = Int
  fromList [] = None
  fromList (x :: xs) = Cons x (fromList xs)

||| A Zipper implementation for Lists
||| inspired by
||| https://hackage.haskell.org/package/ListZipper-1.2.0.2/docs/src/Data-List-Zipper.html
module Data.List.Zipper

%default total
%access public export

||| A Zipper for Lists
data Zipper: Type -> Type where
  Zip: List a -> List a -> Zipper a

%name Zipper z1, z2

-- Implementations
--------------------------------------------------------------------------------

Functor Zipper where
  map f (Zip xs ys) = Zip (map f xs) (map f ys)

Foldable Zipper where
  foldr f acc (Zip xs ys) = foldr f acc (reverse xs ++ ys)

Show a => Show (Zipper a) where
  show (Zip xs []) = show $ reverse xs
  show (Zip xs (x :: ys)) = unwords [show $ reverse xs, "-", show x, "-", show ys]

||| Equality for Zippers
||| Two zipper are equal if they zip the same list and point to the same cursor
Eq a => Eq (Zipper a) where
  (==) (Zip xs ys) (Zip zs ws) = (xs == zs) && (ys == ws)
-- Functions
--------------------------------------------------------------------------------

||| creates an empty Zipper
||| ```idris example
||| empty {a = Nat}
||| ```
empty: Zipper a
empty = Zip [] []

||| checks whether this Zipper is empty
||| ```idris example
||| isEmpty empty {a = Nat}
||| ```
isEmpty: Zipper a -> Bool
isEmpty (Zip [] []) = True
isEmpty _ = False

||| creates a Zipper from a List
||| ```idris example
||| show $ fromList [1,2,3,4,5]
||| ```
fromList: List a -> Zipper a
fromList xs = Zip [] xs

||| moves the cursor to the right or leaves the cursor unchanged
||| ```idris example
|||  show $ right $ fromList [1,2,3,4,5]
||| ```
right: Zipper a -> Zipper a
right (Zip xs (x :: ys)) = Zip (x :: xs) ys
right z = z

||| moves the cursor to the left or leaves the cursor unchanged
||| ```idris example
||| show $ left $ fromList [1,2,3,4,5]
||| ```
left: Zipper a -> Zipper a
left (Zip (x :: xs) ys) = Zip xs (x :: ys)
left z = z

||| gets the element at the current cursor
||| ```idris example
||| cursor $ fromList [1,2,3,4,5]
||| ```
cursor: Zipper a -> Maybe a
cursor (Zip xs ys) = listToMaybe ys

||| move the cursor to the start of the Zipper
||| ```idris example
||| show $ start $ fromList [1,2,3,4,5]
||| ```
start: Zipper a -> Zipper a
start (Zip xs ys) = Zip [] (reverse xs ++ ys)

||| move the cursor to the end of the Zipper
||| ```idris example
||| show $ end $ fromList [1,2,3,4,5]
||| ```
end: Zipper a -> Zipper a
end (Zip xs ys) = Zip (reverse ys ++ xs) []

||| checks whether the cursor is at the start of the Zipper
||| ```idris example
||| startp $ fromList [1,2,3,4,5]
||| ```
startp: Zipper a -> Bool
startp (Zip [] ys) = True
startp _ = False

||| checks whether the cursor is at the end of the Zipper
||| ```idris example
||| endp $ fromList [1,2,3,4,5]
||| ```
endp: Zipper a -> Bool
endp (Zip xs []) = True
endp _ = False

||| inserts an element at the current cursor
||| ```idris example
||| show $ insert 0 $ fromList [1,2,3,4,5]
||| ```
insert: a -> Zipper a -> Zipper a
insert x (Zip xs ys) = Zip xs (x :: ys)

||| push an element into the Zipper and move the cursor past it
||| ```idris example
||| show $ push 0 $ fromList [1,2,3,4,5]
||| ```
push: a -> Zipper a -> Zipper a
push x (Zip xs ys) = Zip (x :: xs) (ys)

||| pop an element from the Zipper
||| ```idris example
||| show $ pop $ right $ fromList [1,2,3,4,5]
||| ```
pop: Zipper a -> Zipper a
pop (Zip (_ :: xs) ys) = Zip xs ys
pop z = z

||| delete the element at the current cursor
||| ```idris example
||| show $ Data.List.Zipper.delete $ fromList [1,2,3,4,5]
||| ```
delete: Zipper a -> Zipper a
delete (Zip xs (x :: ys)) = Zip xs ys
delete z = z

||| remove an element from the zipper
||| ```idris example
||| show $ replace 9 $ fromList[1,2,3,4,5]
||| ```
replace: a -> Zipper a -> Zipper a
replace x (Zip xs (_ :: ys)) = Zip xs (x :: ys)
replace _ z1 = z1

||| Return the index of the current cursor
||| ```idris example
||| index $ fromList [1,2,3,4,5]
||| ```
index: Zipper a -> Nat
index (Zip xs ys) = length xs

||| convert this Zipper to a list
||| ```idris example
||| toList $ fromList[1,2,3,4,5]
||| ```
toList: Zipper a -> List a
toList (Zip xs ys) = reverse xs ++ ys

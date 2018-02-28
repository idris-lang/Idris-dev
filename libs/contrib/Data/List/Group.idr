module Data.List.Group

%default total
%access export

||| The groupBy function returns a list of lists such that the concatenation
||| of the list is equal to the argument, and each sublist contains only
||| elements that are equal according to the user-supplied predicate.
|||
||| ```idris example
||| groupBy (==) [1, 1, 2, 3, 3]
||| ```
|||
groupBy : (a -> a -> Bool) -> List a -> List (List a)
groupBy _ [] = []
groupBy p list@(x :: xs) =
  let (ys, zs) = span (p x) xs in
    (x :: ys) :: groupBy p (assert_smaller list zs)

||| The group function is a special case of groupBy.
|||
||| ```idris example
||| group [1, 1, 2, 3, 3]
||| ```
|||
group : Eq a => List a -> List (List a)
group = groupBy (==)

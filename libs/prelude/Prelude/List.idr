module Prelude.List

import Builtins

import Prelude.Algebra
import Prelude.Basics
import Prelude.Bool
import Prelude.Classes
import Prelude.Foldable
import Prelude.Functor
import Prelude.Maybe
import Prelude.Nat

%access public
%default total

infix 5 \\
infixr 7 ::,++

||| Linked lists
%elim data List a =
  ||| The empty list
  Nil |
  ||| Cons cell
  (::) a (List a)

-- Name hints for interactive editing
%name List xs, ys, zs, ws

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

||| Returns `True` iff the argument is empty
isNil : List a -> Bool
isNil []      = True
isNil (x::xs) = False

||| Returns `True` iff the argument is not empty
isCons : List a -> Bool
isCons []      = False
isCons (x::xs) = True

--------------------------------------------------------------------------------
-- Length
--------------------------------------------------------------------------------

||| Compute the length of a list.
|||
||| Runs in linear time
length : List a -> Nat
length []      = 0
length (x::xs) = 1 + length xs

--------------------------------------------------------------------------------
-- Indexing into lists
--------------------------------------------------------------------------------

||| Find a particular element of a list.
|||
||| @ ok a proof that the index is within bounds
index : (n : Nat) -> (l : List a) -> (ok : lt n (length l) = True) -> a
index Z     (x::xs) p    = x
index (S n) (x::xs) p    = index n xs ?indexTailProof
index _     []      Refl   impossible

||| Attempt to find a particular element of a list.
|||
||| If the provided index is out of bounds, return Nothing.
index' : (n : Nat) -> (l : List a) -> Maybe a
index' Z     (x::xs) = Just x
index' (S n) (x::xs) = index' n xs
index' _     []      = Nothing

||| Get the first element of a non-empty list
||| @ ok proof that the list is non-empty
head : (l : List a) -> {auto ok : isCons l = True} -> a
head []      {ok=Refl}   impossible
head (x::xs) {ok=p}    = x

||| Attempt to get the first element of a list. If the list is empty, return
||| `Nothing`.
head' : (l : List a) -> Maybe a
head' []      = Nothing
head' (x::xs) = Just x

||| Get the tail of a non-empty list.
||| @ ok proof that the list is non-empty
tail : (l : List a) -> {auto ok : isCons l = True} -> List a
tail []      {ok=Refl}   impossible
tail (x::xs) {ok=p}    = xs

||| Attempt to get the tail of a list.
|||
||| If the list is empty, return `Nothing`.
tail' : (l : List a) -> Maybe (List a)
tail' []      = Nothing
tail' (x::xs) = Just xs

||| Retrieve the last element of a non-empty list.
||| @ ok proof that the list is non-empty
last : (l : List a) -> {auto ok : isCons l = True} -> a
last []         {ok=Refl}   impossible
last [x]        {ok=p}    = x
last (x::y::ys) {ok=p}    = last (y::ys) {ok=Refl}

||| Attempt to retrieve the last element of a non-empty list.
|||
||| If the list is empty, return `Nothing`.
last' : (l : List a) -> Maybe a
last' []      = Nothing
last' (x::xs) =
  case xs of
    []      => Just x
    y :: ys => last' xs

||| Return all but the last element of a non-empty list.
||| @ ok proof that the list is non-empty
init : (l : List a) -> {auto ok : isCons l = True} -> List a
init []         {ok=Refl}   impossible
init [x]        {ok=p}    = []
init (x::y::ys) {ok=p}    = x :: init (y::ys) {ok=Refl}

||| Attempt to Return all but the last element of a list.
|||
||| If the list is empty, return `Nothing`.
init' : (l : List a) -> Maybe (List a)
init' []      = Nothing
init' (x::xs) =
  case xs of
    []    => Just []
    y::ys =>
      -- XXX: Problem with typechecking a "do" block here
      case init' $ y::ys of
        Nothing => Nothing
        Just j  => Just $ x :: j

--------------------------------------------------------------------------------
-- Sublists
--------------------------------------------------------------------------------

||| Take the first `n` elements of `xs`
|||
||| If there are not enough elements, return the whole list.
||| @ n how many elements to take
||| @ xs the list to take them from
take : (n : Nat) -> (xs : List a) -> List a
take Z     xs      = []
take (S n) []      = []
take (S n) (x::xs) = x :: take n xs

||| Drop the first `n` elements of `xs`
|||
||| If there are not enough elements, return the empty list.
||| @ n how many elements to drop
||| @ xs the list to drop them from
drop : (n : Nat) -> (xs : List a) -> List a
drop Z     xs      = xs
drop (S n) []      = []
drop (S n) (x::xs) = drop n xs

||| Take the longest prefix of a list such that all elements satisfy some
||| Boolean predicate.
|||
||| @ p the predicate
takeWhile : (p : a -> Bool) -> List a -> List a
takeWhile p []      = []
takeWhile p (x::xs) = if p x then x :: takeWhile p xs else []

||| Remove the longest prefix of a list such that all removed elements satisfy some
||| Boolean predicate.
|||
||| @ p the predicate
dropWhile : (p : a -> Bool) -> List a -> List a
dropWhile p []      = []
dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs

--------------------------------------------------------------------------------
-- Misc.
--------------------------------------------------------------------------------

||| Simply-typed recursion operator for lists.
|||
||| @ nil what to return at the end of the list
||| @ cons what to do at each step of recursion
||| @ xs the list to recurse over
list : (nil : Lazy b) -> (cons : Lazy (a -> List a -> b)) -> (xs : List a) -> b
list nil cons []      = nil
list nil cons (x::xs) = (Force cons) x xs

--------------------------------------------------------------------------------
-- Building (bigger) lists
--------------------------------------------------------------------------------

||| Append two lists
(++) : List a -> List a -> List a
(++) []      right = right
(++) (x::xs) right = x :: (xs ++ right)

||| Construct a list with `n` copies of `x`
||| @ n how many copies
||| @ x the element to replicate
replicate : (n : Nat) -> (x : a) -> List a
replicate Z     x = []
replicate (S n) x = x :: replicate n x

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance (Eq a) => Eq (List a) where
  (==) []      []      = True
  (==) (x::xs) (y::ys) =
    if x == y then
      xs == ys
    else
      False
  (==) _ _ = False


instance Ord a => Ord (List a) where
  compare [] [] = EQ
  compare [] _ = LT
  compare _ [] = GT
  compare (x::xs) (y::ys) =
    if x /= y then
      compare x y
    else
      compare xs ys

instance Semigroup (List a) where
  (<+>) = (++)

instance Monoid (List a) where
  neutral = []

instance Functor List where
  map f []      = []
  map f (x::xs) = f x :: map f xs

--------------------------------------------------------------------------------
-- Zips and unzips
--------------------------------------------------------------------------------

||| Combine two lists of the same length elementwise using some function.
||| @ f the function to combine elements with
||| @ l the first list
||| @ r the second list
||| @ ok a proof that the lengths of the inputs are equal
zipWith : (f : a -> b -> c) -> (l : List a) -> (r : List b) ->
  (ok : length l = length r) -> List c
zipWith f []      (y::ys) Refl   impossible
zipWith f (x::xs) []      Refl   impossible
zipWith f []      []      p    = []
zipWith f (x::xs) (y::ys) p    = f x y :: (zipWith f xs ys ?zipWithTailProof)

||| Combine three lists of the same length elementwise using some function.
||| @ f the function to combine elements with
||| @ x the first list
||| @ y the second list
||| @ z the third list
||| @ ok a proof that the lengths of the first two inputs are equal
||| @ ok' a proof that the lengths of the second and third inputs are equal
zipWith3 : (f : a -> b -> c -> d) -> (x : List a) -> (y : List b) ->
  (z : List c) -> (ok : length x = length y) -> (ok' : length y = length z) -> List d
zipWith3 f _       []      (z::zs) p    Refl   impossible
zipWith3 f _       (y::ys) []      p    Refl   impossible
zipWith3 f []      (y::ys) _       Refl q      impossible
zipWith3 f (x::xs) []      _       Refl q      impossible
zipWith3 f []      []      []      p    q    = []
zipWith3 f (x::xs) (y::ys) (z::zs) p    q    =
  f x y z :: (zipWith3 f xs ys zs ?zipWith3TailProof ?zipWith3TailProof')

||| Combine two lists elementwise into pairs
zip : (l : List a) -> (r : List b) -> (length l = length r) -> List (a, b)
zip = zipWith (\x,y => (x, y))

||| Combine three lists elementwise into tuples
zip3 : (x : List a) -> (y : List b) -> (z : List c) -> (length x = length y) ->
  (length y = length z) -> List (a, b, c)
zip3 = zipWith3 (\x,y,z => (x, y, z))

||| Split a list of pairs into two lists
unzip : List (a, b) -> (List a, List b)
unzip []           = ([], [])
unzip ((l, r)::xs) with (unzip xs)
  | (lefts, rights) = (l::lefts, r::rights)

||| Split a list of triples into three lists
unzip3 : List (a, b, c) -> (List a, List b, List c)
unzip3 []              = ([], [], [])
unzip3 ((l, c, r)::xs) with (unzip3 xs)
  | (lefts, centres, rights) = (l::lefts, c::centres, r::rights)

--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

||| Apply a partial function to the elements of a list, keeping the ones at which
||| it is defined.
mapMaybe : (a -> Maybe b) -> List a -> List b
mapMaybe f []      = []
mapMaybe f (x::xs) =
  case f x of
    Nothing => mapMaybe f xs
    Just j  => j :: mapMaybe f xs

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

instance Foldable List where
  foldr c n [] = n
  foldr c n (x::xs) = c x (foldr c n xs)
  
  foldl f q [] = q
  foldl f q (x::xs) = foldl f (f q x) xs

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

||| Convert any Foldable structure to a list.
toList : Foldable t => t a -> List a
toList = foldr (::) []

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

||| Return the elements of a list in reverse order.
reverse : List a -> List a
reverse = reverse' []
  where
    reverse' : List a -> List a -> List a
    reverse' acc []      = acc
    reverse' acc (x::xs) = reverse' (x::acc) xs

||| Insert some separator between the elements of a list.
|||
||| ````idris example
||| with List (intersperse ',' ['a', 'b', 'c', 'd', 'e'])
||| ````
|||
intersperse : a -> List a -> List a
intersperse sep []      = []
intersperse sep (x::xs) = x :: intersperse' sep xs
  where
    intersperse' : a -> List a -> List a
    intersperse' sep []      = []
    intersperse' sep (y::ys) = sep :: y :: intersperse' sep ys

intercalate : List a -> List (List a) -> List a
intercalate sep l = concat $ intersperse sep l

||| Transposes rows and columns of a list of lists.
|||
||| ```idris example
||| with List transpose [[1, 2], [3, 4]]
||| ```
|||
||| This also works for non square scenarios, thus
||| involution does not always hold:
|||
|||     transpose [[], [1, 2]] = [[1], [2]]
|||     transpose (transpose [[], [1, 2]]) = [[1, 2]]
|||
||| TODO: Solution which satisfies the totality checker?
%assert_total
transpose : List (List a) -> List (List a)
transpose [] = []
transpose ([] :: xss) = transpose xss
transpose ((x::xs) :: xss) = (x :: (mapMaybe head' xss)) :: (transpose (xs :: (map (drop 1) xss)))

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

||| Check if something is a member of a list using a custom comparison.
elemBy : (a -> a -> Bool) -> a -> List a -> Bool
elemBy p e []      = False
elemBy p e (x::xs) =
  if p e x then
    True
  else
    elemBy p e xs

||| Check if something is a member of a list using the default Boolean equality.
elem : Eq a => a -> List a -> Bool
elem = elemBy (==)

||| Find associated information in a list using a custom comparison.
lookupBy : (a -> a -> Bool) -> a -> List (a, b) -> Maybe b
lookupBy p e []      = Nothing
lookupBy p e (x::xs) =
  let (l, r) = x in
    if p e l then
      Just r
    else
      lookupBy p e xs

||| Find associated information in a list using Boolean equality.
lookup : Eq a => a -> List (a, b) -> Maybe b
lookup = lookupBy (==)

||| Check if any elements of the first list are found in the second, using
||| a custom comparison.
hasAnyBy : (a -> a -> Bool) -> List a -> List a -> Bool
hasAnyBy p elems []      = False
hasAnyBy p elems (x::xs) =
  if elemBy p x elems then
    True
  else
    hasAnyBy p elems xs

||| Check if any elements of the first list are found in the second, using
||| Boolean equality.
hasAny : Eq a => List a -> List a -> Bool
hasAny = hasAnyBy (==)

--------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------

||| Find the first element of a list that satisfies a predicate, or `Nothing` if none do.
find : (a -> Bool) -> List a -> Maybe a
find p []      = Nothing
find p (x::xs) =
  if p x then
    Just x
  else
    find p xs

||| Find the index of the first element of a list that satisfies a predicate, or
||| `Nothing` if none do.
findIndex : (a -> Bool) -> List a -> Maybe Nat
findIndex = findIndex' Z
  where
    findIndex' : Nat -> (a -> Bool) -> List a -> Maybe Nat
    findIndex' cnt p []      = Nothing
    findIndex' cnt p (x::xs) =
      if p x then
        Just cnt
      else
        findIndex' (S cnt) p xs

||| Find the indices of all elements that satisfy some predicate.
findIndices : (a -> Bool) -> List a -> List Nat
findIndices = findIndices' Z
  where
    findIndices' : Nat -> (a -> Bool) -> List a -> List Nat
    findIndices' cnt p []      = []
    findIndices' cnt p (x::xs) =
      if p x then
        cnt :: findIndices' (S cnt) p xs
      else
        findIndices' (S cnt) p xs

elemIndexBy : (a -> a -> Bool) -> a -> List a -> Maybe Nat
elemIndexBy p e = findIndex $ p e

elemIndex : Eq a => a -> List a -> Maybe Nat
elemIndex = elemIndexBy (==)

elemIndicesBy : (a -> a -> Bool) -> a -> List a -> List Nat
elemIndicesBy p e = findIndices $ p e

elemIndices : Eq a => a -> List a -> List Nat
elemIndices = elemIndicesBy (==)

--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------

||| filter, applied to a predicate and a list, returns the list of those elements that satisfy the predicate; e.g.,
|||
||| ````idris example
||| filter (< 3) [Z, S Z, S (S Z), S (S (S Z)), S (S (S (S Z)))]
||| ````
|||
filter : (a -> Bool) -> List a -> List a
filter p []      = []
filter p (x::xs) =
  if p x then
    x :: filter p xs
  else
    filter p xs

||| The nubBy function behaves just like nub, except it uses a user-supplied equality predicate instead of the overloaded == function.
nubBy : (a -> a -> Bool) -> List a -> List a
nubBy = nubBy' []
  where
    nubBy' : List a -> (a -> a -> Bool) -> List a -> List a
    nubBy' acc p []      = []
    nubBy' acc p (x::xs) =
      if elemBy p x acc then
        nubBy' acc p xs
      else
        x :: nubBy' (x::acc) p xs

||| O(n^2). The nub function removes duplicate elements from a list. In
||| particular, it keeps only the first occurrence of each element. It is a
||| special case of nubBy, which allows the programmer to supply their own
||| equality test.
|||
||| ```idris example
||| nub (the (List _) [1,2,1,3])
||| ```
nub : Eq a => List a -> List a
nub = nubBy (==)

||| The deleteBy function behaves like delete, but takes a user-supplied equality predicate.
deleteBy : (a -> a -> Bool) -> a -> List a -> List a
deleteBy _  _ []      = []
deleteBy eq x (y::ys) = if x `eq` y then ys else y :: deleteBy eq x ys

||| `delete x` removes the first occurrence of `x` from its list argument. For
||| example,
|||
|||````idris example
|||delete 'a' ['b', 'a', 'n', 'a', 'n', 'a']
|||````
|||
||| It is a special case of deleteBy, which allows the programmer to supply
||| their own equality test.
delete : (Eq a) => a -> List a -> List a
delete = deleteBy (==)

||| The `\\` function is list difference (non-associative). In the result of
||| `xs \\ ys`, the first occurrence of each element of ys in turn (if any) has
||| been removed from `xs`, e.g.,
|||
||| ```idris example
||| (([1,2] ++ [2,3]) \\ [1,2])
||| ```
(\\) : (Eq a) => List a -> List a -> List a
(\\) =  foldl (flip delete)

||| The unionBy function returns the union of two lists by user-supplied equality predicate.
unionBy : (a -> a -> Bool) -> List a -> List a -> List a
unionBy eq xs ys = xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

||| Compute the union of two lists according to their `Eq` instance.
|||
||| ```idris example
||| union ['d', 'o', 'g'] ['c', 'o', 'w']
||| ```
|||
union : (Eq a) => List a -> List a -> List a
union = unionBy (==)

--------------------------------------------------------------------------------
-- Splitting and breaking lists
--------------------------------------------------------------------------------

||| Given a list and a predicate, returns a pair consisting of the longest
||| prefix of the list that satisfies a predicate and the rest of the list.
|||
||| ```idris example
||| span (<3) [1,2,3,2,1]
||| ```
span : (a -> Bool) -> List a -> (List a, List a)
span p []      = ([], [])
span p (x::xs) =
  if p x then
    let (ys, zs) = span p xs in
      (x::ys, zs)
  else
    ([], x::xs)

||| Given a list and a predicate, returns a pair consisting of the longest
||| prefix of the list that does not satisfy a predicate and the rest of the
||| list.
|||
||| ```idris example
||| break (>=3) [1,2,3,2,1]
||| ```
break : (a -> Bool) -> List a -> (List a, List a)
break p = span (not . p)

||| Split on any elements that satisfy the given predicate.
|||
||| ```idris example
||| split (<2) [2,0,3,1,4]
||| ```
split : (a -> Bool) -> List a -> List (List a)
split p xs =
  case break p xs of
    (chunk, [])          => [chunk]
    (chunk, (c :: rest)) => chunk :: split p (assert_smaller xs rest)

||| A tuple where the first element is a List of the n first elements and
||| the second element is a List of the remaining elements of the list
||| It is equivalent to (take n xs, drop n xs)
||| @ n   the index to split at
||| @ xs  the list to split in two
splitAt : (n : Nat) -> (xs : List a) -> (List a, List a)
splitAt n xs = (take n xs, drop n xs)

||| The partition function takes a predicate a list and returns the pair of lists of elements which do and do not satisfy the predicate, respectively; e.g.,
|||
||| ```idris example
||| partition (<3) [0, 1, 2, 3, 4, 5]
||| ```
partition : (a -> Bool) -> List a -> (List a, List a)
partition p []      = ([], [])
partition p (x::xs) =
  let (lefts, rights) = partition p xs in
    if p x then
      (x::lefts, rights)
    else
      (lefts, x::rights)

||| The inits function returns all initial segments of the argument, shortest
||| first. For example,
|||
||| ```idris example
||| inits [1,2,3]
||| ```
inits : List a -> List (List a)
inits xs = [] :: case xs of
  []        => []
  x :: xs'  => map (x ::) (inits xs')

||| The tails function returns all final segments of the argument, longest
||| first. For example,
|||
||| ```idris example
||| tails [1,2,3] == [[1,2,3], [2,3], [3], []]
|||```
tails : List a -> List (List a)
tails xs = xs :: case xs of
  []        => []
  _ :: xs'  => tails xs'

||| Split on the given element.
|||
||| ```idris example
||| splitOn 0 [1,0,2,0,0,3]
||| ```
|||
splitOn : Eq a => a -> List a -> List (List a)
splitOn a = split (== a)

||| Replaces all occurences of the first argument with the second argument in a list.
|||
||| ```idris example
||| replaceOn '-' ',' ['1', '-', '2', '-', '3']
||| ```
|||
replaceOn : Eq a => a -> a -> List a -> List a
replaceOn a b l = map (\c => if c == a then b else c) l

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

isPrefixOfBy : (a -> a -> Bool) -> List a -> List a -> Bool
isPrefixOfBy p [] right        = True
isPrefixOfBy p left []         = False
isPrefixOfBy p (x::xs) (y::ys) =
  if p x y then
    isPrefixOfBy p xs ys
  else
    False

||| The isPrefixOf function takes two lists and returns True iff the first list is a prefix of the second.
isPrefixOf : Eq a => List a -> List a -> Bool
isPrefixOf = isPrefixOfBy (==)

isSuffixOfBy : (a -> a -> Bool) -> List a -> List a -> Bool
isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)

||| The isSuffixOf function takes two lists and returns True iff the first list is a suffix of the second.
isSuffixOf : Eq a => List a -> List a -> Bool
isSuffixOf = isSuffixOfBy (==)

||| The isInfixOf function takes two lists and returns True iff the first list is contained, wholly and intact, anywhere within the second.
|||
||| ```idris example
||| isInfixOf ['b','c'] ['a', 'b', 'c', 'd']
||| ```
||| ```idris example
||| isInfixOf ['b','d'] ['a', 'b', 'c', 'd']
||| ```
|||
isInfixOf : Eq a => List a -> List a -> Bool
isInfixOf n h = any (isPrefixOf n) (tails h)

--------------------------------------------------------------------------------
-- Sorting
--------------------------------------------------------------------------------

sorted : Ord a => List a -> Bool
sorted []      = True
sorted (x::xs) =
  case xs of
    Nil     => True
    (y::ys) => x <= y && sorted (y::ys)

mergeBy : (a -> a -> Ordering) -> List a -> List a -> List a
mergeBy order []      right   = right
mergeBy order left    []      = left
mergeBy order (x::xs) (y::ys) =
  if order x y == LT 
     then x :: mergeBy order xs (y::ys)
     else y :: mergeBy order (x::xs) ys

merge : Ord a => List a -> List a -> List a
merge = mergeBy compare

sort : Ord a => List a -> List a
sort []  = []
sort [x] = [x]
sort xs  = let (x, y) = split xs in
    merge (sort (assert_smaller xs x)) 
          (sort (assert_smaller xs y)) -- not structurally smaller, hence assert
  where
    splitRec : List a -> List a -> (List a -> List a) -> (List a, List a)
    splitRec (_::_::xs) (y::ys) zs = splitRec xs ys (zs . ((::) y))
    splitRec _          ys      zs = (zs [], ys)

    split : List a -> (List a, List a)
    split xs = splitRec xs xs id

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

||| Either return the head of a list, or `Nothing` if it is empty.
listToMaybe : List a -> Maybe a
listToMaybe []      = Nothing
listToMaybe (x::xs) = Just x

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

catMaybes : List (Maybe a) -> List a
catMaybes []      = []
catMaybes (x::xs) =
  case x of
    Nothing => catMaybes xs
    Just j  => j :: catMaybes xs

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

||| The empty list is a right identity for append.
appendNilRightNeutral : (l : List a) ->
  l ++ [] = l
appendNilRightNeutral []      = Refl
appendNilRightNeutral (x::xs) =
  let inductiveHypothesis = appendNilRightNeutral xs in
    ?appendNilRightNeutralStepCase

||| Appending lists is associative.
appendAssociative : (l : List a) -> (c : List a) -> (r : List a) ->
  l ++ (c ++ r) = (l ++ c) ++ r
appendAssociative []      c r = Refl
appendAssociative (x::xs) c r =
  let inductiveHypothesis = appendAssociative xs c r in
    ?appendAssociativeStepCase

||| The length of two lists that are appended is the sum of the lengths
||| of the input lists.
lengthAppend : (left : List a) -> (right : List a) ->
  length (left ++ right) = length left + length right
lengthAppend []      right = Refl
lengthAppend (x::xs) right =
  let inductiveHypothesis = lengthAppend xs right in
    ?lengthAppendStepCase

||| Mapping a function over a list doesn't change its length.
mapPreservesLength : (f : a -> b) -> (l : List a) ->
  length (map f l) = length l
mapPreservesLength f []      = Refl
mapPreservesLength f (x::xs) =
  let inductiveHypothesis = mapPreservesLength f xs in
    ?mapPreservesLengthStepCase

||| Mapping a function over two lists and appending them is equivalent
||| to appending them and then mapping the function.
mapDistributesOverAppend : (f : a -> b) -> (l : List a) -> (r : List a) ->
  map f (l ++ r) = map f l ++ map f r
mapDistributesOverAppend f []      r = Refl
mapDistributesOverAppend f (x::xs) r =
  let inductiveHypothesis = mapDistributesOverAppend f xs r in
    ?mapDistributesOverAppendStepCase

||| Mapping two functions is the same as mapping their composition.
mapFusion : (f : b -> c) -> (g : a -> b) -> (l : List a) ->
  map f (map g l) = map (f . g) l
mapFusion f g []      = Refl
mapFusion f g (x::xs) =
  let inductiveHypothesis = mapFusion f g xs in
    ?mapFusionStepCase

||| No list contains an element of the empty list by any predicate.
hasAnyByNilFalse : (p : a -> a -> Bool) -> (l : List a) ->
  hasAnyBy p [] l = False
hasAnyByNilFalse p []      = Refl
hasAnyByNilFalse p (x::xs) =
  let inductiveHypothesis = hasAnyByNilFalse p xs in
    ?hasAnyByNilFalseStepCase

||| No list contains an element of the empty list.
hasAnyNilFalse : Eq a => (l : List a) -> hasAny [] l = False
hasAnyNilFalse l = ?hasAnyNilFalseBody

foldlAsFoldr : (b -> a -> b) -> b -> List a -> b
foldlAsFoldr f z t = foldr (flip (.) . flip f) id t z

||| The definition of foldl works the same as the default definition
||| in terms of foldr
foldlMatchesFoldr : (f : b -> a -> b) -> (q : b) -> (xs : List a) -> foldl f q xs = foldlAsFoldr f q xs
foldlMatchesFoldr f q [] = Refl
foldlMatchesFoldr f q (x :: xs) = foldlMatchesFoldr f (f q x) xs


--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

indexTailProof = proof {
  intros;
  rewrite sym p;
  trivial;
}

lengthAppendStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

hasAnyNilFalseBody = proof {
    intros;
    rewrite (hasAnyByNilFalse (==) l);
    trivial;
}

hasAnyByNilFalseStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

appendNilRightNeutralStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

appendAssociativeStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

mapFusionStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

mapDistributesOverAppendStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

mapPreservesLengthStepCase = proof {
    intros;
    rewrite inductiveHypothesis;
    trivial;
}

zipWithTailProof = proof {
    intros;
    rewrite (succInjective (length xs) (length ys) p);
    trivial;
}

zipWith3TailProof = proof {
    intros;
    rewrite (succInjective (length xs) (length ys) p);
    trivial;
}

zipWith3TailProof' = proof {
    intros;
    rewrite (succInjective (length ys) (length zs) q);
    trivial;
}


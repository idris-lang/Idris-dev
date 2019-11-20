module Data.Vect

import public Data.Fin
import Language.Reflection

%access public export
%default total

infixr 7 ::

||| Vectors: Generic lists with explicit length in the type
||| @ len the length of the list
||| @ elem the type of elements
data Vect : (len : Nat) -> (elem : Type) -> Type where
  ||| Empty vector
  Nil  : Vect Z elem
  ||| A non-empty vector of length `S len`, consisting of a head element and
  ||| the rest of the list, of length `len`.
  (::) : (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem

-- Hints for interactive editing
%name Vect xs,ys,zs,ws

--------------------------------------------------------------------------------
-- Length
--------------------------------------------------------------------------------

||| Calculate the length of a `Vect`.
|||
||| **Note**: this is only useful if you don't already statically know the length
||| and you want to avoid matching the implicit argument for erasure reasons.
||| @ len the length (provably equal to the return value)
||| @ xs the vector
length : (xs : Vect len elem) -> Nat
length [] = 0
length (x::xs) = 1 + length xs

||| Show that the length function on vectors in fact calculates the length
private lengthCorrect : (len : Nat) -> (xs : Vect len elem) -> length xs = len
lengthCorrect Z     []        = Refl
lengthCorrect (S n) (x :: xs) = rewrite lengthCorrect n xs in Refl

--------------------------------------------------------------------------------
-- Indexing into vectors
--------------------------------------------------------------------------------

||| All but the first element of the vector
|||
||| ```idris example
||| tail [1,2,3,4]
||| ```
tail : Vect (S len) elem -> Vect len elem
tail (x::xs) = xs

||| Only the first element of the vector
|||
||| ```idris example
||| head [1,2,3,4]
||| ```
head : Vect (S len) elem -> elem
head (x::xs) = x

||| The last element of the vector
|||
||| ```idris example
||| last [1,2,3,4]
||| ```
last : Vect (S len) elem -> elem
last (x::[])    = x
last (x::y::ys) = last $ y::ys

||| All but the last element of the vector
|||
||| ```idris example
||| init [1,2,3,4]
||| ```
init : Vect (S len) elem -> Vect len elem
init (x::[])    = []
init (x::y::ys) = x :: init (y::ys)

||| Extract a particular element from a vector
|||
||| ```idris example
||| index 1 [1,2,3,4]
||| ```
index : Fin len -> Vect len elem -> elem
index FZ     (x::xs) = x
index (FS k) (x::xs) = index k xs


||| Insert an element at a particular index
|||
||| ```idris example
||| insertAt 1 8 [1,2,3,4]
||| ```
insertAt : Fin (S len) -> elem -> Vect len elem -> Vect (S len) elem
insertAt FZ     y xs      = y :: xs
insertAt (FS k) y (x::xs) = x :: insertAt k y xs
insertAt (FS k) y []      = absurd k

||| Construct a new vector consisting of all but the indicated element
|||
||| ```idris example
||| deleteAt 1 [1,2,3,4]
||| ```
deleteAt : Fin (S len) -> Vect (S len) elem -> Vect len elem
deleteAt             FZ     (x::xs) = xs
deleteAt {len = S m} (FS k) (x::xs) = x :: deleteAt k xs
deleteAt {len = Z}   (FS k) (x::xs) = absurd k
deleteAt             _      []      impossible

||| Replace an element at a particlar index with another
|||
||| ```idris example
||| replaceAt 1 8 [1,2,3,4]
||| ```
replaceAt : Fin len -> elem -> Vect len elem -> Vect len elem
replaceAt FZ     y (x::xs) = y :: xs
replaceAt (FS k) y (x::xs) = x :: replaceAt k y xs

||| Replace the element at a particular index with the result of applying a function to it
||| @ i the index to replace at
||| @ f the update function
||| @ xs the vector to replace in
|||
||| ```idris example
||| updateAt 1 (+10) [1,2,3,4]
||| ```
updateAt : (i : Fin len) -> (f : elem -> elem) -> (xs : Vect len elem) -> Vect len elem
updateAt FZ     f (x::xs) = f x :: xs
updateAt (FS k) f (x::xs) = x :: updateAt k f xs

--------------------------------------------------------------------------------
-- Subvectors
--------------------------------------------------------------------------------

||| Get the first n elements of a Vect
||| @ n the number of elements to take
|||
||| ```idris example
||| take 2 [1,2,3,4]
||| ```
take : (n : Nat) -> Vect (n + m) elem -> Vect n elem
take Z     xs        = []
take (S k) (x :: xs) = x :: take k xs

||| Remove the first n elements of a Vect
||| @ n the number of elements to remove
|||
||| ```idris example
||| drop 2 [1,2,3,4]
||| ```
drop : (n : Nat) -> Vect (n + m) elem -> Vect m elem
drop Z     xs        = xs
drop (S k) (x :: xs) = drop k xs

||| Take up to the first n elements of a Vect if they exist.
||| @ n the maximum number of elements to take
|||
||| ```idris example
||| takeUpto 10 [1,2,3,4]
||| ```
takeUpto : (x : Nat) -> Vect n elem -> Vect (minimum x n) elem
takeUpto Z ys = []
takeUpto x [] = rewrite minimumZeroZeroLeft x in []
takeUpto (S x) (y::ys) = y :: takeUpto x ys

||| Drop up to the first n elements of a Vect if they exist.
||| @ n the maximum number of elements to remove.
|||
||| ```idris example
||| dropUpto 10 [1,2,3,4]
||| ```
dropUpto : (x : Nat) -> Vect n elem -> Vect (n `minus` minimum x n) elem
dropUpto Z ys {n} = rewrite minusZeroRight n in ys
dropUpto x [] = []
dropUpto (S x) (y :: ys) = dropUpto x ys

||| Take the longest prefix of a Vect such that all elements satisfy some
||| Boolean predicate.
|||
||| @ p the predicate
|||
||| ```idris example
||| takeWhile (<3) [1,2,3,4]
||| ```
takeWhile : (p : elem -> Bool) -> Vect len elem -> (q ** Vect q elem)
takeWhile p []      = (_ ** [])
takeWhile p (x::xs) =
  let (len ** ys) = takeWhile p xs
  in if p x then
      (S len ** x :: ys)
    else
      (_ ** [])

||| Remove the longest prefix of a Vect such that all removed elements satisfy some
||| Boolean predicate.
|||
||| @ p the predicate
|||
||| ```idris example
||| dropWhile (<3) [1,2,3,4]
||| ```
dropWhile : (p : elem -> Bool) -> Vect len elem -> (q ** Vect q elem)
dropWhile p [] = (_ ** [])
dropWhile p (x::xs) =
  if p x then
    dropWhile p xs
  else
    (_ ** x::xs)

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

||| Reverse the order of the elements of a vector
|||
||| ```idris example
||| reverse [1,2,3,4]
||| ```
reverse : Vect len elem -> Vect len elem
reverse xs = go [] xs
  where go : Vect n elem -> Vect m elem -> Vect (n+m) elem
        go {n}         acc []        = rewrite plusZeroRightNeutral n in acc
        go {n} {m=S m} acc (x :: xs) = rewrite sym $ plusSuccRightSucc n m
                                       in go (x::acc) xs

||| Alternate an element between the other elements of a vector
||| @ sep the element to intersperse
||| @ xs the vector to separate with `sep`
|||
||| ```idris example
||| intersperse 0 [1,2,3,4]
||| ```
intersperse : (sep : elem) -> (xs : Vect len elem) -> Vect (len + pred len) elem
intersperse sep []      = []
intersperse sep (x::xs) = x :: intersperse' sep xs
  where
    intersperse' : elem -> Vect n elem -> Vect (n + n) elem
    intersperse'         sep []      = []
    intersperse' {n=S n} sep (x::xs) = rewrite sym $ plusSuccRightSucc n n
                                       in sep :: x :: intersperse' sep xs

--------------------------------------------------------------------------------
-- Conversion from list (toList is provided by Foldable)
--------------------------------------------------------------------------------


fromList' : Vect len elem -> (l : List elem) -> Vect (length l + len) elem
fromList' ys [] = ys
fromList' {len} ys (x::xs) =
  rewrite (plusSuccRightSucc (length xs) len) ==>
          Vect (plus (length xs) (S len)) elem in
  fromList' (x::ys) xs

||| Convert a list to a vector.
|||
||| The length of the list should be statically known.
|||
||| ```idris example
||| fromList [1,2,3,4]
||| ```
fromList : (l : List elem) -> Vect (length l) elem
fromList l =
  rewrite (sym $ plusZeroRightNeutral (length l)) in
  reverse $ fromList' [] l

--------------------------------------------------------------------------------
-- Building (bigger) vectors
--------------------------------------------------------------------------------

||| Append two vectors
|||
||| ```idris example
||| [1,2,3,4] ++ [5,6]
||| ```
(++) : (xs : Vect m elem) -> (ys : Vect n elem) -> Vect (m + n) elem
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys

||| Repeat some value some number of times.
|||
||| @ len the number of times to repeat it
||| @ x the value to repeat
|||
||| ```idris example
||| replicate 4 1
||| ```
replicate : (len : Nat) -> (x : elem) -> Vect len elem
replicate Z     x = []
replicate (S k) x = x :: replicate k x

||| Merge two ordered vectors
|||
||| ```idris example
||| mergeBy compare (fromList [1,3,5]) (fromList [2,3,4,5,6])
||| ```
mergeBy : (elem -> elem -> Ordering) -> (xs : Vect n elem) -> (ys : Vect m elem) -> Vect (n + m) elem
mergeBy order [] [] = []
mergeBy order [] (x :: xs) = x :: xs
mergeBy {n = S k} order (x :: xs) [] = rewrite plusZeroRightNeutral (S k) in
                                               x :: xs
mergeBy {n = S k} {m = S k'} order (x :: xs) (y :: ys)
     = case order x y of
            LT => x :: mergeBy order xs (y :: ys)
            _  => rewrite sym (plusSuccRightSucc k k') in
                             y :: mergeBy order (x :: xs) ys

merge : Ord elem => Vect n elem -> Vect m elem -> Vect (n + m) elem
merge = mergeBy compare

--------------------------------------------------------------------------------
-- Zips and unzips
--------------------------------------------------------------------------------

||| Combine two equal-length vectors pairwise with some function.
|||
||| @ f the function to combine elements with
||| @ xs the first vector of elements
||| @ ys the second vector of elements
|||
||| ```idris example
||| zipWith (+) (fromList [1,2,3,4]) (fromList [5,6,7,8])
||| ```
zipWith : (f : a -> b -> c) -> (xs : Vect n a) -> (ys : Vect n b) -> Vect n c
zipWith f []      []      = []
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

||| Combine three equal-length vectors into a vector with some function
|||
||| ```idris example
||| zipWith3 (\x,y,z => x+y+z) (fromList [1,2,3,4]) (fromList [5,6,7,8]) (fromList [1,1,1,1])
||| ```
zipWith3 : (a -> b -> c -> d) -> (xs : Vect n a) -> (ys : Vect n b) -> (zs : Vect n c) -> Vect n d
zipWith3 f []      []      []      = []
zipWith3 f (x::xs) (y::ys) (z::zs) = f x y z :: zipWith3 f xs ys zs

||| Combine two equal-length vectors pairwise
|||
||| ```idris example
||| zip (fromList [1,2,3,4]) (fromList [1,2,3,4])
||| ```
zip : (xs : Vect n a) -> (ys : Vect n b) -> Vect n (a, b)
zip = zipWith (\x,y => (x,y))

||| Combine three equal-length vectors elementwise into a vector of tuples
|||
||| ```idris example
||| zip3 (fromList [1,2,3,4]) (fromList [1,2,3,4]) (fromList [1,2,3,4])
||| ```
zip3 : (xs : Vect n a) -> (ys : Vect n b) -> (zs : Vect n c) -> Vect n (a, b, c)
zip3 = zipWith3 (\x,y,z => (x,y,z))

||| Convert a vector of pairs to a pair of vectors
|||
||| ```idris example
||| unzip (fromList [(1,2), (1,2)])
||| ```
unzip : (xs : Vect n (a, b)) -> (Vect n a, Vect n b)
unzip []           = ([], [])
unzip ((l, r)::xs) with (unzip xs)
  | (lefts, rights) = (l::lefts, r::rights)

||| Convert a vector of three-tuples to a triplet of vectors
|||
||| ```idris example
||| unzip3 (fromList [(1,2,3), (1,2,3)])
||| ```
unzip3 : (xs : Vect n (a, b, c)) -> (Vect n a, Vect n b, Vect n c)
unzip3 []            = ([], [], [])
unzip3 ((l,c,r)::xs) with (unzip3 xs)
  | (lefts, centers, rights) = (l::lefts, c::centers, r::rights)

--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

implementation (Eq elem) => Eq (Vect len elem) where
  (==) []      []      = True
  (==) (x::xs) (y::ys) = x == y && xs == ys


||| Compare two vectors of potentially different length for equality.
|||
vecEq : Eq type => Vect n type -> Vect m type -> Bool
vecEq [] [] = True
vecEq [] (x :: xs) = False
vecEq (x :: xs) [] = False
vecEq (x :: xs) (y :: ys) = x == y && vecEq xs ys

--------------------------------------------------------------------------------
-- Order
--------------------------------------------------------------------------------

implementation Ord elem => Ord (Vect len elem) where
  compare []      []      = EQ
  compare (x::xs) (y::ys) = compare x y `thenCompare` compare xs ys


--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

implementation Functor (Vect n) where
  map f []        = []
  map f (x::xs) = f x :: map f xs


||| Map a partial function across a vector, returning those elements for which
||| the function had a value.
|||
||| The first projection of the resulting pair (ie the length) will always be
||| at most the length of the input vector. This is not, however, guaranteed
||| by the type.
|||
||| @ f the partial function (expressed by returning `Maybe`)
||| @ xs the vector to check for results
|||
||| ```idris example
||| mapMaybe ((find (=='a')) . unpack) (fromList ["abc","ade","bgh","xyz"])
||| ```
mapMaybe : (f : a -> Maybe b) -> (xs : Vect len a) -> (m : Nat ** Vect m b)
mapMaybe f []      = (_ ** [])
mapMaybe f (x::xs) =
  let (len ** ys) = mapMaybe f xs
  in case f x of
       Just y  => (S len ** y :: ys)
       Nothing => (  len **      ys)

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

foldrImpl : (t -> acc -> acc) -> acc -> (acc -> acc) -> Vect n t -> acc
foldrImpl f e go [] = go e
foldrImpl f e go (x::xs) = foldrImpl f e (go . (f x)) xs

implementation Foldable (Vect n) where
  foldr f e xs = foldrImpl f e id xs

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

||| Flatten a vector of equal-length vectors
|||
||| ```idris example
||| concat [[1,2,3], [4,5,6]]
||| ```
concat : (xss : Vect m (Vect n elem)) -> Vect (m * n) elem
concat []      = []
concat (v::vs) = v ++ concat vs

||| Foldr without seeding the accumulator
|||
||| ```idris example
||| foldr1 (-) (fromList [1,2,3])
||| ```
foldr1 : (t -> t -> t) -> Vect (S n) t -> t
foldr1 f [x]        = x
foldr1 f (x::y::xs) = f x (foldr1 f (y::xs))

||| Foldl without seeding the accumulator
|||
||| ```idris example
||| foldl1 (-) (fromList [1,2,3])
||| ```
foldl1 : (t -> t -> t) -> Vect (S n) t -> t
foldl1 f (x::xs) = foldl f x xs

--------------------------------------------------------------------------------
-- Scans
--------------------------------------------------------------------------------

||| The scanl function is similar to foldl, but returns all the intermediate
||| accumulator states in the form of a vector.
|||
||| ```idris example
||| scanl (-) 0 (fromList [1,2,3])
||| ```
scanl : (res -> elem -> res) -> res -> Vect len elem -> Vect (S len) res
scanl f q []      = [q]
scanl f q (x::xs) = q :: scanl f (f q x) xs

||| The scanl1 function is a variant of scanl that doesn't require an explicit
||| starting value.
||| It assumes the first element of the vector to be the starting value and then
||| starts the fold with the element following it.
|||
||| ```idris example
||| scanl1 (-) (fromList [1,2,3])
||| ```
scanl1 : (elem -> elem -> elem) -> Vect len elem -> Vect len elem
scanl1 f [] = []
scanl1 f (x::xs) = scanl f x xs

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

||| Search for an item using a user-provided test
||| @ p the equality test
||| @ e the item to search for
||| @ xs the vector to search in
|||
||| ```idris example
||| elemBy (==) 2 [1,2,3,4]
||| ```
elemBy : (p : elem -> elem -> Bool) -> (e : elem) -> (xs : Vect len elem) -> Bool
elemBy p e []      = False
elemBy p e (x::xs) = p e x || elemBy p e xs

||| Use the default Boolean equality on elements to search for an item
||| @ x what to search for
||| @ xs where to search
|||
||| ```idris example
||| elem 3 [1,2,3,4]
||| ```
elem : Eq elem => (x : elem) -> (xs : Vect len elem) -> Bool
elem = elemBy (==)

||| Find the association of some key with a user-provided comparison
||| @ p the comparison operator for keys (True if they match)
||| @ e the key to look for
|||
||| ```idris example
||| lookupBy (==) 2 [(1, 'a'), (2, 'b'), (3, 'c')]
||| ```
lookupBy : (p : key -> key -> Bool) -> (e : key) -> (xs : Vect n (key, val)) -> Maybe val
lookupBy p e []           = Nothing
lookupBy p e ((l, r)::xs) = if p e l then Just r else lookupBy p e xs

||| Find the assocation of some key using the default Boolean equality test
|||
||| ```idris example
||| lookup 3 [(1, 'a'), (2, 'b'), (3, 'c')]
||| ```
lookup : Eq key => key -> Vect n (key, val) -> Maybe val
lookup = lookupBy (==)

||| Check if any element of xs is found in elems by a user-provided comparison
||| @ p the comparison operator
||| @ elems the vector to search
||| @ xs what to search for
|||
||| ```idris example
||| hasAnyBy (==) [2,5] [1,2,3,4]
||| ```
hasAnyBy : (p : elem -> elem -> Bool) -> (elems : Vect m elem) -> (xs : Vect len elem) -> Bool
hasAnyBy p elems []      = False
hasAnyBy p elems (x::xs) = elemBy p x elems || hasAnyBy p elems xs

||| Check if any element of xs is found in elems using the default Boolean equality test
|||
||| ```idris example
||| hasAny [2,5] [1,2,3,4]
||| ```
hasAny : Eq elem => Vect m elem -> Vect len elem -> Bool
hasAny = hasAnyBy (==)

--------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------

||| Find the first element of the vector that satisfies some test
||| @ p the test to satisfy
|||
||| ```idris example
||| find (== 3) [1,2,3,4]
||| ```
find : (p : elem -> Bool) -> (xs : Vect len elem) -> Maybe elem
find p []      = Nothing
find p (x::xs) = if p x then Just x else find p xs

||| Find the index of the first element of the vector that satisfies some test
|||
||| ```idris example
||| findIndex (== 3) [1,2,3,4]
||| ```
findIndex : (elem -> Bool) -> Vect len elem -> Maybe (Fin len)
findIndex p []        = Nothing
findIndex p (x :: xs) = if p x then Just 0 else map FS (findIndex p xs)

||| Find the indices of all elements that satisfy some test
|||
||| ```idris example
||| findIndices (< 3) [1,2,3,4]
||| ```
findIndices : (elem -> Bool) -> Vect m elem -> List (Fin m)
findIndices p []        = []
findIndices p (x :: xs) = let is = map FS $ findIndices p xs
                           in if p x then 0 :: is else is

||| Find the index of the first element of the vector that satisfies some test
|||
||| ```idris example
||| elemIndexBy (==) 3 [1,2,3,4]
||| ```
elemIndexBy : (elem -> elem -> Bool) -> elem -> Vect m elem -> Maybe (Fin m)
elemIndexBy p e = findIndex $ p e

||| Find the index of the first element of the vector equal to the given one.
|||
||| ```idris example
||| elemIndex 3 [1,2,3,4]
||| ```
elemIndex : Eq elem => elem -> Vect m elem -> Maybe (Fin m)
elemIndex = elemIndexBy (==)

||| Find the indices of all elements that satisfy some test
|||
||| ```idris example
||| elemIndicesBy (<=) 3 [1,2,3,4]
||| ```
elemIndicesBy : (elem -> elem -> Bool) -> elem -> Vect m elem -> List (Fin m)
elemIndicesBy p e = findIndices $ p e

||| Find the indices of all elements uquals to the given one
|||
||| ```idris example
||| elemIndices 3 [1,2,3,4,3]
||| ```
elemIndices : Eq elem => elem -> Vect m elem -> List (Fin m)
elemIndices = elemIndicesBy (==)

--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------

||| Find all elements of a vector that satisfy some test
|||
||| ```idris example
||| filter (< 3) (fromList [1,2,3,4])
||| ```
filter : (elem -> Bool) -> Vect len elem -> (p ** Vect p elem)
filter p []      = ( _ ** [] )
filter p (x::xs) =
  let (_ ** tail) = filter p xs
   in if p x then
        (_ ** x::tail)
      else
        (_ ** tail)

||| Make the elements of some vector unique by some test
|||
||| ```idris example
||| nubBy (==) (fromList [1,2,2,3,4,4])
||| ```
nubBy : (elem -> elem -> Bool) -> Vect len elem -> (p ** Vect p elem)
nubBy = nubBy' []
  where
    nubBy' : Vect m elem -> (elem -> elem -> Bool) -> Vect len elem -> (p ** Vect p elem)
    nubBy' acc p []      = (_ ** [])
    nubBy' acc p (x::xs) with (elemBy p x acc)
      | True  = nubBy' acc p xs
      | False with (nubBy' (x::acc) p xs)
        | (_ ** tail) = (_ ** x::tail)

||| Make the elements of some vector unique by the default Boolean equality
|||
||| ```idris example
||| nub (fromList [1,2,2,3,4,4])
||| ```
nub : Eq elem => Vect len elem -> (p ** Vect p elem)
nub = nubBy (==)

||| Delete first element from list according to some test
|||
||| ```idris example
||| deleteBy (<) 3 (fromList [1,2,2,3,4,4])
||| ```
deleteBy : (elem -> elem -> Bool) -> elem -> Vect len elem -> (p ** Vect p elem)
deleteBy _  _ []      = (_ ** [])
deleteBy eq x (y::ys) =
  let (len ** zs) = deleteBy eq x ys
  in if x `eq` y then (_ ** ys) else (S len ** y ::zs)

||| Delete first element from list equal to the given one
|||
||| ```idris example
||| delete 2 (fromList [1,2,2,3,4,4])
||| ```
delete : (Eq elem) => elem -> Vect len elem -> (p ** Vect p elem)
delete = deleteBy (==)

--------------------------------------------------------------------------------
-- Splitting and breaking lists
--------------------------------------------------------------------------------

||| A tuple where the first element is a `Vect` of the `n` first elements and
||| the second element is a `Vect` of the remaining elements of the original.
||| It is equivalent to `(take n xs, drop n xs)` (`splitAtTakeDrop`),
||| but is more efficient.
|||
||| @ n   the index to split at
||| @ xs  the `Vect` to split in two
|||
||| ```idris example
||| splitAt 2 (fromList [1,2,3,4])
||| ```
splitAt : (n : Nat) -> (xs : Vect (n + m) elem) -> (Vect n elem, Vect m elem)
splitAt Z xs = ([], xs)
splitAt (S k) (x :: xs) with (splitAt k xs)
  | (tk, dr) = (x :: tk, dr)

||| A tuple where the first element is a `Vect` of the `n` elements passing given test
||| and the second element is a `Vect` of the remaining elements of the original.
|||
||| ```idris example
||| partition (== 2) (fromList [1,2,3,2,4])
||| ```
partition : (elem -> Bool) -> Vect len elem -> ((p ** Vect p elem), (q ** Vect q elem))
partition p []      = ((_ ** []), (_ ** []))
partition p (x::xs) =
  let ((leftLen ** lefts), (rightLen ** rights)) = partition p xs in
    if p x then
      ((S leftLen ** x::lefts), (rightLen ** rights))
    else
      ((leftLen ** lefts), (S rightLen ** x::rights))

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

||| Verify vector prefix
|||
||| ```idris example
||| isPrefixOfBy (==) (fromList [1,2]) (fromList [1,2,3,4])
||| ```
isPrefixOfBy : (elem -> elem -> Bool) -> Vect m elem -> Vect len elem -> Bool
isPrefixOfBy p [] right        = True
isPrefixOfBy p left []         = False
isPrefixOfBy p (x::xs) (y::ys) = p x y && isPrefixOfBy p xs ys

||| Verify vector prefix
|||
||| ```idris example
||| isPrefixOf (fromList [1,2]) (fromList [1,2,3,4])
||| ```
isPrefixOf : Eq elem => Vect m elem -> Vect len elem -> Bool
isPrefixOf = isPrefixOfBy (==)

||| Verify vector suffix
|||
||| ```idris example
||| isSuffixOfBy (==) (fromList [3,4]) (fromList [1,2,3,4])
||| ```
isSuffixOfBy : (elem -> elem -> Bool) -> Vect m elem -> Vect len elem -> Bool
isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)

||| Verify vector suffix
|||
||| ```idris example
||| isSuffixOf (fromList [3,4]) (fromList [1,2,3,4])
||| ```
isSuffixOf : Eq elem => Vect m elem -> Vect len elem -> Bool
isSuffixOf = isSuffixOfBy (==)

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

||| Convert Maybe type into Vect
|||
||| ```idris example
||| maybeToVect (Just 2)
||| ```
maybeToVect : Maybe elem -> (p ** Vect p elem)
maybeToVect Nothing  = (_ ** [])
maybeToVect (Just j) = (_ ** [j])

||| Convert first element of Vect (if exists) into Maybe.
|||
||| ```idris example
||| vectToMaybe [2]
||| ```
vectToMaybe : Vect len elem -> Maybe elem
vectToMaybe []      = Nothing
vectToMaybe (x::xs) = Just x

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

||| Filter out Nothings from Vect
|||
||| ```idris example
||| catMaybes [Just 1, Just 2, Nothing, Nothing, Just 5]
||| ```
catMaybes : Vect n (Maybe elem) -> (p ** Vect p elem)
catMaybes []             = (_ ** [])
catMaybes (Nothing::xs)  = catMaybes xs
catMaybes ((Just j)::xs) =
  let (_ ** tail) = catMaybes xs
   in (_ ** j::tail)

||| Get diagonal elements
|||
||| ```idris example
||| diag [[1,2,3], [4,5,6], [7,8,9]]
||| ```
diag : Vect len (Vect len elem) -> Vect len elem
diag []             = []
diag ((x::xs)::xss) = x :: diag (map tail xss)

range : {len : Nat} -> Vect len (Fin len)
range {len=Z}   = []
range {len=S _} = FZ :: map FS range

||| Transpose a `Vect` of `Vect`s, turning rows into columns and vice versa.
|||
||| This is like zipping all the inner `Vect`s together and is equivalent to `traverse id` (`transposeTraverse`).
|||
||| As the types ensure rectangularity, this is an involution, unlike `Prelude.List.transpose`.
|||
||| ```idris example
||| transpose [[1,2], [3,4], [5,6], [7,8]]
||| ```
transpose : Vect m (Vect n elem) -> Vect n (Vect m elem)
transpose []        = replicate _ []                -- = [| [] |]
transpose (x :: xs) = zipWith (::) x (transpose xs) -- = [| x :: xs |]

--------------------------------------------------------------------------------
-- Applicative/Monad/Traversable
--------------------------------------------------------------------------------

implementation Applicative (Vect k) where
    pure = replicate _
    fs <*> vs = zipWith apply fs vs

||| This monad is different from the List monad, (>>=)
||| uses the diagonal.
implementation Monad (Vect len) where
    m >>= f = diag (map f m)

implementation Traversable (Vect n) where
    traverse f []        = [| [] |]
    traverse f (x :: xs) = [| f x :: traverse f xs |]

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

implementation Show elem => Show (Vect len elem) where
    show = show . toList

--------------------------------------------------------------------------------
-- Uninhabited
--------------------------------------------------------------------------------

Uninhabited a => Uninhabited (Vect (S n) a) where
    uninhabited (x :: _) = uninhabited x

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

vectMustBeNil : (xs : Vect Z a) -> xs = []
vectMustBeNil [] = Refl

vectConsCong : (x : elem) -> (xs : Vect len elem) -> (ys : Vect m elem) -> (xs = ys) -> (x :: xs = x :: ys)
vectConsCong x xs xs Refl = Refl

vectInjective1 : {xs : Vect n a} -> {ys : Vect m b} -> x :: xs ~=~ y :: ys -> x ~=~ y
vectInjective1 Refl = Refl

vectInjective2 : {xs : Vect n a} -> {ys : Vect m b} -> x :: xs ~=~ y :: ys -> xs ~=~ ys
vectInjective2 Refl = Refl

vectNilRightNeutral : (xs : Vect n a) -> xs ++ [] = xs
vectNilRightNeutral [] = Refl
vectNilRightNeutral (x :: xs) =
  vectConsCong _ _ _ (vectNilRightNeutral xs)

vectAppendAssociative : (xs : Vect xLen elem) ->
                        (ys : Vect yLen elem) ->
                        (zs : Vect zLen elem) ->
                        xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
vectAppendAssociative [] y z = Refl
vectAppendAssociative (x :: xs) ys zs =
  vectConsCong _ _ _ (vectAppendAssociative xs ys zs)

||| Adding a prefix and then taking the prefix gets the prefix. Or,
||| adding a suffix and then dropping the suffix does nothing.
takePrefix : (ns : Vect n a) -> (ms : Vect m a) -> take n (ns ++ ms) = ns
takePrefix [] _ = Refl
takePrefix (n :: ns) ms = cong $ takePrefix ns ms

||| Adding a prefix and then dropping the prefix does nothing. Or,
||| adding a suffix and then taking the suffix gets the suffix.
dropPrefix : (ns : Vect n a) -> (ms : Vect m a) -> drop n (ns ++ ms) = ms
dropPrefix [] ms = Refl
dropPrefix (_ :: ns) ms = dropPrefix ns ms

||| `take n . take (n + m) = take n`
takeTake : (n : Nat) -> (m : Nat) ->
           (xs : Vect ((n + m) + l) a) -> (ys : Vect (n + (m + l)) a) ->
           xs ~=~ ys ->
           take n (take (n + m) xs) = take n ys
takeTake Z m _ _ _ = Refl
takeTake (S n) m (x :: xs) (y :: ys) prf = rewrite vectInjective1 prf in cong (takeTake n m xs ys (vectInjective2 prf))

||| `drop (n + m) = drop m . drop n`
dropDrop : (n : Nat) -> (m : Nat) ->
           (xs : Vect ((n + m) + l) a) -> (ys : Vect (n + (m + l)) a) ->
           xs ~=~ ys ->
           drop (n + m) xs = drop m (drop n ys)
dropDrop Z m xs xs Refl = Refl
dropDrop (S n) m (_ :: xs) (_ :: ys) prf = dropDrop n m xs ys (vectInjective2 prf)

||| A `Vect` may be restored from its components.
takeDropConcat : (n : Nat) -> (xs : Vect (n + m) a) -> take n xs ++ drop n xs = xs
takeDropConcat Z xs = Refl
takeDropConcat (S n) (x :: xs) = cong $ takeDropConcat n xs

||| `drop n . take (n + m) = take m . drop n`.
|||
||| Or: there are two ways to extract a subsequence.
dropTakeTakeDrop : (n : Nat) -> (m : Nat) ->
                   (xs : Vect ((n + m) + l) a) -> (ys : Vect (n + (m + l)) a) ->
                   xs ~=~ ys ->
                   drop n (take (n + m) xs) = take m (drop n ys)
dropTakeTakeDrop Z m xs xs Refl = Refl
dropTakeTakeDrop (S n) m (_ :: xs) (_ :: ys) prf = dropTakeTakeDrop n m xs ys (vectInjective2 prf)

splitAtTakeDrop : (n : Nat) -> (xs : Vect (n + m) a) -> splitAt n xs = (take n xs, drop n xs)
splitAtTakeDrop Z xs = Refl
splitAtTakeDrop (S k) (x :: xs) with (splitAt k xs) proof p
  | (tk, dr) = let prf = trans p (splitAtTakeDrop k xs)
                in aux (cong {f=(x ::) . fst} prf) (cong {f=snd} prf)
  where aux : {a, b : Type} -> {w, x : a} -> {y, z : b} -> w = x -> y = z -> (w, y) = (x, z)
        aux Refl Refl = Refl

zipWithIsLiftA2 : (f : a -> b -> c) -> (as : Vect n a) -> (bs : Vect n b) -> zipWith f as bs = [| f as bs |]
zipWithIsLiftA2 _ [] [] = Refl
zipWithIsLiftA2 f (a :: as) (b :: bs) = rewrite zipWithIsLiftA2 f as bs in Refl
zipWithIsLiftA3 : (f : a -> b -> c -> d) -> (as : Vect n a) -> (bs : Vect n b) -> (cs : Vect n c) -> zipWith3 f as bs cs = [| f as bs cs |]
zipWithIsLiftA3 _ [] [] [] = Refl
zipWithIsLiftA3 f (a :: as) (b :: bs) (c :: cs) = rewrite zipWithIsLiftA3 f as bs cs in Refl

-- Note relationship to Applicative (Morphism (Fin n))
indexReplicate : (x : a) -> (n : Nat) -> (i : Fin n) -> index i (replicate n x) = x
indexReplicate x (S n) FZ = Refl
indexReplicate x (S n) (FS i) = indexReplicate x n i
indexZipWith : (f : a -> b -> c) -> (as : Vect n a) -> (bs : Vect n b) -> (i : Fin n) -> index i (zipWith f as bs) = f (index i as) (index i bs)
indexZipWith f (a :: _) (b :: _) FZ = Refl
indexZipWith f (_ :: as) (_ :: bs) (FS i) = indexZipWith f as bs i
indexTranspose : (x : Fin o) -> (y : Fin i) -> (xss : Vect o (Vect i a)) -> index y (index x xss) = index x (index y (transpose xss))
indexTranspose x y (xs :: xss) = rewrite prf in
                                 rewrite sym $ indexZipWith Vect.(::) xs (transpose xss) y in Refl
  where prf : index y (index x (xs :: xss)) = index x (index y xs :: index y (transpose xss))
        prf = case x of
                   FZ => Refl
                   FS k => indexTranspose k y xss

transposeTraverse : (xss : Vect o (Vect i a)) -> transpose xss = traverse Basics.id xss
transposeTraverse [] = Refl
transposeTraverse (xs :: xss) = rewrite zipWithIsLiftA2 Vect.(::) xs (transpose xss) in cong (transposeTraverse xss)

traverseIdCons : (xs : Vect o a) -> (xss : Vect o (Vect i a)) -> traverse Basics.id [| xs :: xss |] = xs :: traverse Basics.id xss
traverseIdCons [] [] = Refl
traverseIdCons (x :: xs) (ys :: xss) = rewrite traverseIdCons xs xss in Refl
transposeCons : (xs : Vect o a) -> (xss : Vect o (Vect i a)) -> transpose (zipWith (::) xs xss) = xs :: transpose xss
transposeCons xs xss = rewrite zipWithIsLiftA2 Vect.(::) xs xss in rewrite transposeTraverse (pure (::) <*> xs <*> xss) in rewrite transposeTraverse xss in traverseIdCons xs xss

--------------------------------------------------------------------------------
-- DecEq
--------------------------------------------------------------------------------

implementation DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (x :: ys)   | Yes Refl with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | Yes Refl | Yes Refl = Yes Refl
      decEq (x :: xs) (x :: ys) | Yes Refl | No  neq  = No (neq . vectInjective2)
    decEq (x :: xs) (y :: ys)   | No  neq             = No (neq . vectInjective1)

{- The following definition is elaborated in a wrong case-tree. Examination pending.
implementation DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) with (decEq x y, decEq xs ys)
    decEq (x :: xs) (x :: xs) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (x :: xs) (y :: ys) | (_, No nEqTl) = No (\p => nEqTl (vectInjective2 p))
    decEq (x :: xs) (y :: ys) | (No nEqHd, _) = No (\p => nEqHd (vectInjective1 p))
-}

namespace DiffLength

  ||| A wrapper function to compare two vectors of potentially
  ||| different length with proof that the lengths are equal.
  decEqWithProof : DecEq a
                => (prf : n = m)
                -> (xs  : Vect n a)
                -> (ys  : Vect m a)
                -> Dec (xs = ys)
  decEqWithProof Refl xs ys with (decEq xs ys)
    decEqWithProof Refl ys ys | (Yes Refl)  = Yes Refl
    decEqWithProof Refl xs ys | (No contra) = No contra

  vectorsDiffLength : DecEq a
                   => (contra : (n = m) -> Void)
                   -> {xs : Vect n a}
                   -> {ys : Vect m a}
                   -> (xs = ys) -> Void
  vectorsDiffLength contra Refl = contra Refl

  ||| Decidable equality of two vectors of potentially different length.
  decEq : DecEq a
       => (xs : Vect n a)
       -> (ys : Vect m a)
       -> Dec (xs = ys)
  decEq xs ys {n} {m} with (decEq n m)
    decEq xs ys {n = m} {m = m} | (Yes Refl) = decEqWithProof Refl xs ys
    decEq xs ys {n = n} {m = m} | (No contra) = No (vectorsDiffLength contra)



--------------------------------------------------------------------------------
-- Elem
--------------------------------------------------------------------------------

||| A proof that some element is found in a vector
data Elem : a -> Vect k a -> Type where
     Here : Elem x (x::xs)
     There : (later : Elem x xs) -> Elem x (y::xs)

||| Nothing can be in an empty Vect
noEmptyElem : {x : a} -> Elem x [] -> Void
noEmptyElem Here impossible

Uninhabited (Elem x []) where
  uninhabited = noEmptyElem

||| An item not in the head and not in the tail is not in the Vect at all
neitherHereNorThere : {x, y : a} -> {xs : Vect n a} -> Not (x = y) -> Not (Elem x xs) -> Not (Elem x (y :: xs))
neitherHereNorThere xneqy xninxs Here = xneqy Refl
neitherHereNorThere xneqy xninxs (There xinxs) = xninxs xinxs

||| A decision procedure for Elem
isElem : DecEq a => (x : a) -> (xs : Vect n a) -> Dec (Elem x xs)
isElem x [] = No noEmptyElem
isElem x (y :: xs) with (decEq x y)
  isElem x (x :: xs) | (Yes Refl) = Yes Here
  isElem x (y :: xs) | (No xneqy) with (isElem x xs)
    isElem x (y :: xs) | (No xneqy) | (Yes xinxs) = Yes (There xinxs)
    isElem x (y :: xs) | (No xneqy) | (No xninxs) = No (neitherHereNorThere xneqy xninxs)

replaceElem : (xs : Vect k t) -> Elem x xs -> (y : t) -> (ys : Vect k t ** Elem y ys)
replaceElem (x::xs) Here y = (y :: xs ** Here)
replaceElem (x::xs) (There xinxs) y with (replaceElem xs xinxs y)
  | (ys ** yinys) = (x :: ys ** There yinys)

replaceByElem : (xs : Vect k t) -> Elem x xs -> t -> Vect k t
replaceByElem (x::xs) Here y = y :: xs
replaceByElem (x::xs) (There xinxs) y = x :: replaceByElem xs xinxs y

mapElem : {xs : Vect k t} -> {f : t -> u} -> Elem x xs -> Elem (f x) (map f xs)
mapElem Here = Here
mapElem (There e) = There (mapElem e)

||| Remove the element at the given position.
|||
||| @xs The vector to be removed from
||| @p A proof that the element to be removed is in the vector
dropElem : (xs : Vect (S k) t) -> (p : Elem x xs) -> Vect k t
dropElem (x :: ys) Here = ys
dropElem {k = (S k)} (x :: ys) (There later) = x :: dropElem ys later

-- Some convenience functions for testing lengths

||| If the given Vect is the required length, return a Vect with that
||| length in its type, otherwise return Nothing
||| @len the required length
||| @xs the vector with the desired length
-- Needs to be Maybe rather than Dec, because if 'n' is unequal to m, we
-- only know we don't know how to make a Vect n a, not that one can't exist.
exactLength : {m : Nat} -> -- expected at run-time
              (len : Nat) -> (xs : Vect m a) -> Maybe (Vect len a)
exactLength {m} len xs with (decEq m len)
  exactLength {m = m} m xs | (Yes Refl) = Just xs
  exactLength {m = m} len xs | (No contra) = Nothing

||| If the given Vect is at least the required length, return a Vect with
||| at least that length in its type, otherwise return Nothing
||| @len the required length
||| @xs the vector with the desired length
overLength : {m : Nat} -> -- expected at run-time
             (len : Nat) -> (xs : Vect m a) -> Maybe (p ** Vect (plus p len) a)
overLength {m} n xs with (cmp m n)
  overLength {m = m} (plus m (S y)) xs | (CmpLT y) = Nothing
  overLength {m = m} m xs | CmpEQ
         = Just (0 ** xs)
  overLength {m = plus n (S x)} n xs | (CmpGT x)
         = Just (S x ** rewrite plusCommutative (S x) n in xs)

module Data.Vect

import public Data.Fin
import Language.Reflection

%access public export
%default total

infixr 7 ::

||| Vectors: Generic lists with explicit length in the type
||| @ len the length of the list
||| @ elem the type of elements
%elim
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
tail : Vect (S len) elem -> Vect len elem
tail (x::xs) = xs

||| Only the first element of the vector
head : Vect (S len) elem -> elem
head (x::xs) = x

||| The last element of the vector
last : Vect (S len) elem -> elem
last (x::[])    = x
last (x::y::ys) = last $ y::ys

||| All but the last element of the vector
init : Vect (S len) elem -> Vect len elem
init (x::[])    = []
init (x::y::ys) = x :: init (y::ys)

||| Extract a particular element from a vector
index : Fin len -> Vect len elem -> elem
index FZ     (x::xs) = x
index (FS k) (x::xs) = index k xs


||| Insert an element at a particular index
insertAt : Fin (S len) -> elem -> Vect len elem -> Vect (S len) elem
insertAt FZ     y xs      = y :: xs
insertAt (FS k) y (x::xs) = x :: insertAt k y xs
insertAt (FS k) y []      = absurd k

||| Construct a new vector consisting of all but the indicated element
deleteAt : Fin (S len) -> Vect (S len) elem -> Vect len elem
deleteAt             FZ     (x::xs) = xs
deleteAt {len = S m} (FS k) (x::xs) = x :: deleteAt k xs
deleteAt {len = Z}   (FS k) (x::xs) = absurd k
deleteAt             _      []      impossible

||| Replace an element at a particlar index with another
replaceAt : Fin len -> elem -> Vect len elem -> Vect len elem
replaceAt FZ     y (x::xs) = y :: xs
replaceAt (FS k) y (x::xs) = x :: replaceAt k y xs

||| Replace the element at a particular index with the result of applying a function to it
||| @ i the index to replace at
||| @ f the update function
||| @ xs the vector to replace in
updateAt : (i : Fin len) -> (f : elem -> elem) -> (xs : Vect len elem) -> Vect len elem
updateAt FZ     f (x::xs) = f x :: xs
updateAt (FS k) f (x::xs) = x :: updateAt k f xs

--------------------------------------------------------------------------------
-- Subvectors
--------------------------------------------------------------------------------

||| Get the first n elements of a Vect
||| @ n the number of elements to take
take : (n : Nat) -> Vect (n + m) elem -> Vect n elem
take Z     xs        = []
take (S k) (x :: xs) = x :: take k xs

||| Remove the first n elements of a Vect
||| @ n the number of elements to remove
drop : (n : Nat) -> Vect (n + m) elem -> Vect m elem
drop Z     xs        = xs
drop (S k) (x :: xs) = drop k xs

||| Take the longest prefix of a Vect such that all elements satisfy some
||| Boolean predicate.
|||
||| @ p the predicate
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
reverse : Vect len elem -> Vect len elem
reverse xs = go [] xs
  where go : Vect n elem -> Vect m elem -> Vect (n+m) elem
        go {n}         acc []        = rewrite plusZeroRightNeutral n in acc
        go {n} {m=S m} acc (x :: xs) = rewrite sym $ plusSuccRightSucc n m
                                       in go (x::acc) xs

||| Alternate an element between the other elements of a vector
||| @ sep the element to intersperse
||| @ xs the vector to separate with `sep`
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
fromList : (l : List elem) -> Vect (length l) elem
fromList l =
  rewrite (sym $ plusZeroRightNeutral (length l)) in
  reverse $ fromList' [] l

--------------------------------------------------------------------------------
-- Building (bigger) vectors
--------------------------------------------------------------------------------

||| Append two vectors
(++) : (xs : Vect m elem) -> (ys : Vect n elem) -> Vect (m + n) elem
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys

||| Repeate some value some number of times.
|||
||| @ len the number of times to repeat it
||| @ x the value to repeat
replicate : (len : Nat) -> (x : elem) -> Vect len elem
replicate Z     x = []
replicate (S k) x = x :: replicate k x

||| Merge two ordered vectors
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
zipWith : (f : a -> b -> c) -> (xs : Vect n a) -> (ys : Vect n b) -> Vect n c
zipWith f []      []      = []
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

||| Combine three equal-length vectors into a vector with some function
zipWith3 : (a -> b -> c -> d) -> (xs : Vect n a) -> (ys : Vect n b) -> (zs : Vect n c) -> Vect n d
zipWith3 f []      []      []      = []
zipWith3 f (x::xs) (y::ys) (z::zs) = f x y z :: zipWith3 f xs ys zs

||| Combine two equal-length vectors pairwise
zip : (xs : Vect n a) -> (ys : Vect n b) -> Vect n (a, b)
zip = zipWith (\x,y => (x,y))

||| Combine three equal-length vectors elementwise into a vector of tuples
zip3 : (xs : Vect n a) -> (ys : Vect n b) -> (zs : Vect n c) -> Vect n (a, b, c)
zip3 = zipWith3 (\x,y,z => (x,y,z))

||| Convert a vector of pairs to a pair of vectors
unzip : (xs : Vect n (a, b)) -> (Vect n a, Vect n b)
unzip []           = ([], [])
unzip ((l, r)::xs) with (unzip xs)
  | (lefts, rights) = (l::lefts, r::rights)

||| Convert a vector of three-tuples to a triplet of vectors
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
concat : (xss : Vect m (Vect n elem)) -> Vect (m * n) elem
concat []      = []
concat (v::vs) = v ++ concat vs

||| Foldr without seeding the accumulator
foldr1 : (t -> t -> t) -> Vect (S n) t -> t
foldr1 f (x::xs) = foldr f x xs

||| Foldl without seeding the accumulator
foldl1 : (t -> t -> t) -> Vect (S n) t -> t
foldl1 f (x::xs) = foldl f x xs
--------------------------------------------------------------------------------
-- Scans
--------------------------------------------------------------------------------

scanl : (res -> elem -> res) -> res -> Vect len elem -> Vect (S len) res
scanl f q []      = [q]
scanl f q (x::xs) = q :: scanl f (f q x) xs

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

||| Search for an item using a user-provided test
||| @ p the equality test
||| @ e the item to search for
||| @ xs the vector to search in
elemBy : (p : elem -> elem -> Bool) -> (e : elem) -> (xs : Vect len elem) -> Bool
elemBy p e []      = False
elemBy p e (x::xs) = p e x || elemBy p e xs

||| Use the default Boolean equality on elements to search for an item
||| @ x what to search for
||| @ xs where to search
elem : Eq elem => (x : elem) -> (xs : Vect len elem) -> Bool
elem = elemBy (==)

||| Find the association of some key with a user-provided comparison
||| @ p the comparison operator for keys (True if they match)
||| @ e the key to look for
lookupBy : (p : key -> key -> Bool) -> (e : key) -> (xs : Vect n (key, val)) -> Maybe val
lookupBy p e []           = Nothing
lookupBy p e ((l, r)::xs) = if p e l then Just r else lookupBy p e xs

||| Find the assocation of some key using the default Boolean equality test
lookup : Eq key => key -> Vect n (key, val) -> Maybe val
lookup = lookupBy (==)

||| Check if any element of xs is found in elems by a user-provided comparison
||| @ p the comparison operator
||| @ elems the vector to search
||| @ xs what to search for
hasAnyBy : (p : elem -> elem -> Bool) -> (elems : Vect m elem) -> (xs : Vect len elem) -> Bool
hasAnyBy p elems []      = False
hasAnyBy p elems (x::xs) = elemBy p x elems || hasAnyBy p elems xs

||| Check if any element of xs is found in elems using the default Boolean equality test
hasAny : Eq elem => Vect m elem -> Vect len elem -> Bool
hasAny = hasAnyBy (==)

--------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------

||| Find the first element of the vector that satisfies some test
||| @ p the test to satisfy
find : (p : elem -> Bool) -> (xs : Vect len elem) -> Maybe elem
find p []      = Nothing
find p (x::xs) = if p x then Just x else find p xs

||| Find the index of the first element of the vector that satisfies some test
findIndex : (elem -> Bool) -> Vect len elem -> Maybe (Fin len)
findIndex p []        = Nothing
findIndex p (x :: xs) = if p x then Just 0 else map FS (findIndex p xs)

||| Find the indices of all elements that satisfy some test
findIndices : (elem -> Bool) -> Vect m elem -> List (Fin m)
findIndices p []        = []
findIndices p (x :: xs) = let is = map FS $ findIndices p xs
                           in if p x then 0 :: is else is

elemIndexBy : (elem -> elem -> Bool) -> elem -> Vect m elem -> Maybe (Fin m)
elemIndexBy p e = findIndex $ p e

elemIndex : Eq elem => elem -> Vect m elem -> Maybe (Fin m)
elemIndex = elemIndexBy (==)

elemIndicesBy : (elem -> elem -> Bool) -> elem -> Vect m elem -> List (Fin m)
elemIndicesBy p e = findIndices $ p e

elemIndices : Eq elem => elem -> Vect m elem -> List (Fin m)
elemIndices = elemIndicesBy (==)

--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------

||| Find all elements of a vector that satisfy some test
filter : (elem -> Bool) -> Vect len elem -> (p ** Vect p elem)
filter p []      = ( _ ** [] )
filter p (x::xs) =
  let (_ ** tail) = filter p xs
   in if p x then
        (_ ** x::tail)
      else
        (_ ** tail)

||| Make the elements of some vector unique by some test
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
nub : Eq elem => Vect len elem -> (p ** Vect p elem)
nub = nubBy (==)

deleteBy : (elem -> elem -> Bool) -> elem -> Vect len elem -> (p ** Vect p elem)
deleteBy _  _ []      = (_ ** [])
deleteBy eq x (y::ys) =
  let (len ** zs) = deleteBy eq x ys
  in if x `eq` y then (_ ** ys) else (S len ** y ::zs)

delete : (Eq elem) => elem -> Vect len elem -> (p ** Vect p elem)
delete = deleteBy (==)

--------------------------------------------------------------------------------
-- Splitting and breaking lists
--------------------------------------------------------------------------------

||| A tuple where the first element is a Vect of the n first elements and
||| the second element is a Vect of the remaining elements of the original Vect
||| It is equivalent to (take n xs, drop n xs)
||| @ n   the index to split at
||| @ xs  the Vect to split in two
splitAt : (n : Nat) -> (xs : Vect (n + m) elem) -> (Vect n elem, Vect m elem)
splitAt n xs = (take n xs, drop n xs)

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

isPrefixOfBy : (elem -> elem -> Bool) -> Vect m elem -> Vect len elem -> Bool
isPrefixOfBy p [] right        = True
isPrefixOfBy p left []         = False
isPrefixOfBy p (x::xs) (y::ys) = p x y && isPrefixOfBy p xs ys

isPrefixOf : Eq elem => Vect m elem -> Vect len elem -> Bool
isPrefixOf = isPrefixOfBy (==)

isSuffixOfBy : (elem -> elem -> Bool) -> Vect m elem -> Vect len elem -> Bool
isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)

isSuffixOf : Eq elem => Vect m elem -> Vect len elem -> Bool
isSuffixOf = isSuffixOfBy (==)

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

maybeToVect : Maybe elem -> (p ** Vect p elem)
maybeToVect Nothing  = (_ ** [])
maybeToVect (Just j) = (_ ** [j])

vectToMaybe : Vect len elem -> Maybe elem
vectToMaybe []      = Nothing
vectToMaybe (x::xs) = Just x

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

catMaybes : Vect n (Maybe elem) -> (p ** Vect p elem)
catMaybes []             = (_ ** [])
catMaybes (Nothing::xs)  = catMaybes xs
catMaybes ((Just j)::xs) =
  let (_ ** tail) = catMaybes xs
   in (_ ** j::tail)

diag : Vect len (Vect len elem) -> Vect len elem
diag []             = []
diag ((x::xs)::xss) = x :: diag (map tail xss)

range : {len : Nat} -> Vect len (Fin len)
range {len=Z}   = []
range {len=S _} = FZ :: map FS range

||| Transpose a Vect of Vects, turning rows into columns and vice versa.
|||
||| As the types ensure rectangularity, this is an involution, unlike `Prelude.List.transpose`.
transpose : {n : Nat} -> Vect m (Vect n elem) -> Vect n (Vect m elem)
transpose []        = replicate _ []
transpose (x :: xs) = zipWith (::) x (transpose xs)

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
    traverse f [] = pure Vect.Nil
    traverse f (x::xs) = [| Vect.(::) (f x) (traverse f xs) |]

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

implementation Show elem => Show (Vect len elem) where
    show = show . toList

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

vectConsCong : (x : elem) -> (xs : Vect len elem) -> (ys : Vect m elem) -> (xs = ys) -> (x :: xs = x :: ys)
vectConsCong x xs xs Refl = Refl

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

--------------------------------------------------------------------------------
-- DecEq
--------------------------------------------------------------------------------

vectInjective1 : {xs, ys : Vect n a} -> {x, y : a} -> x :: xs = y :: ys -> x = y
vectInjective1 {x=x} {y=x} {xs=xs} {ys=xs} Refl = Refl

vectInjective2 : {xs, ys : Vect n a} -> {x, y : a} -> x :: xs = y :: ys -> xs = ys
vectInjective2 {x=x} {y=x} {xs=xs} {ys=xs} Refl = Refl

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

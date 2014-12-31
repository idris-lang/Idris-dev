module Data.VectType 

import Data.Fin

%access public
%default total

namespace Vect {
  
infixr 7 ::

%elim data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : (x : a) -> (xs : Vect n a) -> Vect (S n) a

-- Hints for interactive editing
%name Vect xs,ys,zs,ws

--------------------------------------------------------------------------------
-- Length
--------------------------------------------------------------------------------

||| Calculate the length of a `Vect`.
|||
||| **Note**: this is only useful if you don't already statically know the length
||| and you want to avoid matching the implicit argument for erasure reasons.
||| @ n the length (provably equal to the return value)
||| @ xs the vector
length : (xs : Vect n a) -> Nat
length [] = 0
length (x::xs) = 1 + length xs

||| Show that the length function on vectors in fact calculates the length
private lengthCorrect : (n : Nat) -> (xs : Vect n a) -> length xs = n
lengthCorrect Z     []        = Refl
lengthCorrect (S n) (x :: xs) = rewrite lengthCorrect n xs in Refl

--------------------------------------------------------------------------------
-- Indexing into vectors
--------------------------------------------------------------------------------

||| All but the first element of the vector
tail : Vect (S n) a -> Vect n a
tail (x::xs) = xs

||| Only the first element of the vector
head : Vect (S n) a -> a
head (x::xs) = x

||| The last element of the vector
last : Vect (S n) a -> a
last (x::[])    = x
last (x::y::ys) = last $ y::ys

||| All but the last element of the vector
init : Vect (S n) a -> Vect n a
init (x::[])    = []
init (x::y::ys) = x :: init (y::ys)

||| Extract a particular element from a vector
index : Fin n -> Vect n a -> a
index FZ     (x::xs) = x
index (FS k) (x::xs) = index k xs


||| Insert an element at a particular index
insertAt : Fin (S n) -> a -> Vect n a -> Vect (S n) a
insertAt FZ     y xs      = y :: xs
insertAt (FS k) y (x::xs) = x :: insertAt k y xs
insertAt (FS k) y []      = absurd k

||| Construct a new vector consisting of all but the indicated element
deleteAt : Fin (S n) -> Vect (S n) a -> Vect n a
deleteAt           FZ     (x::xs) = xs
deleteAt {n = S m} (FS k) (x::xs) = x :: deleteAt k xs
deleteAt {n = Z}   (FS k) (x::xs) = absurd k
deleteAt           _      []      impossible

||| Replace an element at a particlar index with another
replaceAt : Fin n -> t -> Vect n t -> Vect n t
replaceAt FZ     y (x::xs) = y :: xs
replaceAt (FS k) y (x::xs) = x :: replaceAt k y xs

||| Replace the element at a particular index with the result of applying a function to it
||| @ i the index to replace at
||| @ f the update function
||| @ xs the vector to replace in
updateAt : (i : Fin n) -> (f : t -> t) -> (xs : Vect n t) -> Vect n t
updateAt FZ     f (x::xs) = f x :: xs
updateAt (FS k) f (x::xs) = x :: updateAt k f xs

--------------------------------------------------------------------------------
-- Subvectors
--------------------------------------------------------------------------------

||| Get the first m elements of a Vect
||| @ m the number of elements to take
take : (n : Nat) -> Vect (n + m) a -> Vect n a
take Z     xs        = []
take (S k) (x :: xs) = x :: take k xs

||| Remove the first m elements of a Vect
||| @ m the number of elements to remove
drop : (n : Nat) -> Vect (n + m) a -> Vect m a
drop Z     xs        = xs
drop (S k) (x :: xs) = drop k xs

||| Take the longest prefix of a Vect such that all elements satisfy some
||| Boolean predicate.
|||
||| @ p the predicate
takeWhile : (p : a -> Bool) -> Vect n a -> (q ** Vect q a)
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
dropWhile : (p : a -> Bool) -> Vect n a -> (q ** Vect q a)
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
reverse : Vect n a -> Vect n a
reverse xs = go [] xs
  where go : Vect n a -> Vect m a -> Vect (n+m) a
        go {n}         acc []        = rewrite plusZeroRightNeutral n in acc
        go {n} {m=S m} acc (x :: xs) = rewrite sym $ plusSuccRightSucc n m
                                       in go (x::acc) xs

||| Alternate an element between the other elements of a vector
||| @ sep the element to intersperse
||| @ xs the vector to separate with `sep`
intersperse : (sep : a) -> (xs : Vect n a) -> Vect (n + pred n) a
intersperse sep []      = []
intersperse sep (x::xs) = x :: intersperse' sep xs
  where
    intersperse' : a -> Vect n a -> Vect (n + n) a
    intersperse'         sep []      = []
    intersperse' {n=S n} sep (x::xs) = rewrite sym $ plusSuccRightSucc n n
                                       in sep :: x :: intersperse' sep xs

--------------------------------------------------------------------------------
-- Conversion from list (toList is provided by Foldable)
--------------------------------------------------------------------------------


fromList' : Vect n a -> (l : List a) -> Vect (length l + n) a
fromList' ys [] = ys
fromList' {n} ys (x::xs) =
  rewrite (plusSuccRightSucc (length xs) n) ==>
          Vect (plus (length xs) (S n)) a in
  fromList' (x::ys) xs

||| Convert a list to a vector.
|||
||| The length of the list should be statically known.
fromList : (l : List a) -> Vect (length l) a
fromList l =
  rewrite (sym $ plusZeroRightNeutral (length l)) in
  reverse $ fromList' [] l

--------------------------------------------------------------------------------
-- Building (bigger) vectors
--------------------------------------------------------------------------------

||| Append two vectors
(++) : Vect m a -> Vect n a -> Vect (m + n) a
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys

||| Repeate some value n times
||| @ n the number of times to repeat it
||| @ x the value to repeat
replicate : (n : Nat) -> (x : a) -> Vect n a
replicate Z     x = []
replicate (S k) x = x :: replicate k x

--------------------------------------------------------------------------------
-- Zips and unzips
--------------------------------------------------------------------------------

||| Combine two equal-length vectors pairwise with some function
zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f []      []      = []
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

||| Combine three equal-length vectors into a vector with some function
zipWith3 : (a -> b -> c -> d) -> Vect n a -> Vect n b -> Vect n c -> Vect n d
zipWith3 f []      []      []      = []
zipWith3 f (x::xs) (y::ys) (z::zs) = f x y z :: zipWith3 f xs ys zs

||| Combine two equal-length vectors pairwise
zip : Vect n a -> Vect n b -> Vect n (a, b)
zip = zipWith (\x,y => (x,y))

||| Combine three equal-length vectors elementwise into a vector of tuples
zip3 : Vect n a -> Vect n b -> Vect n c -> Vect n (a, b, c)
zip3 = zipWith3 (\x,y,z => (x,y,z))

||| Convert a vector of pairs to a pair of vectors
unzip : Vect n (a, b) -> (Vect n a, Vect n b)
unzip []           = ([], [])
unzip ((l, r)::xs) with (unzip xs)
  | (lefts, rights) = (l::lefts, r::rights)

||| Convert a vector of three-tuples to a triplet of vectors
unzip3 : Vect n (a, b, c) -> (Vect n a, Vect n b, Vect n c)
unzip3 []            = ([], [], [])
unzip3 ((l,c,r)::xs) with (unzip3 xs)
  | (lefts, centers, rights) = (l::lefts, c::centers, r::rights)

--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

instance (Eq a) => Eq (Vect n a) where
  (==) []      []      = True
  (==) (x::xs) (y::ys) =
    if x == y then
      xs == ys
    else
      False


--------------------------------------------------------------------------------
-- Order
--------------------------------------------------------------------------------

instance Ord a => Ord (Vect n a) where
  compare []      []      = EQ
  compare (x::xs) (y::ys) =
    if x /= y then
      compare x y
    else
      compare xs ys


--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

instance Functor (Vect n) where
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
mapMaybe : (f : a -> Maybe b) -> (xs : Vect n a) -> (m : Nat ** Vect m b)
mapMaybe f []      = (_ ** [])
mapMaybe f (x::xs) =
  let (len ** ys) = mapMaybe f xs
  in case f x of
       Just y  => (S len ** y :: ys)
       Nothing => (  len **      ys)


--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

total foldrImpl : (t -> acc -> acc) -> acc -> (acc -> acc) -> Vect n t -> acc
foldrImpl f e go [] = go e
foldrImpl f e go (x::xs) = foldrImpl f e (go . (f x)) xs

instance Foldable (Vect n) where
  foldr f e xs = foldrImpl f e id xs

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

||| Flatten a vector of equal-length vectors
concat : Vect m (Vect n a) -> Vect (m * n) a
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

scanl : (b -> a -> b) -> b -> Vect n a -> Vect (S n) b
scanl f q []      = [q]
scanl f q (x::xs) = q :: scanl f (f q x) xs

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

||| Search for an item using a user-provided test
||| @ p the equality test
||| @ e the item to search for
||| @ xs the vector to search in
elemBy : (p : a -> a -> Bool) -> (e : a) -> (xs : Vect n a) -> Bool
elemBy p e []      = False
elemBy p e (x::xs) with (p e x)
  | True  = True
  | False = elemBy p e xs

||| Use the default Boolean equality on elements to search for an item
||| @ x what to search for
||| @ xs where to search
elem : Eq a => (x : a) -> (xs : Vect n a) -> Bool
elem = elemBy (==)

||| Find the association of some key with a user-provided comparison
||| @ p the comparison operator for keys (True if they match)
||| @ e the key to look for
lookupBy : (p : a -> a -> Bool) -> (e : a) -> (xs : Vect n (a, b)) -> Maybe b
lookupBy p e []           = Nothing
lookupBy p e ((l, r)::xs) with (p e l)
  | True  = Just r
  | False = lookupBy p e xs

||| Find the assocation of some key using the default Boolean equality test
lookup : Eq a => a -> Vect n (a, b) -> Maybe b
lookup = lookupBy (==)

||| Check if any element of xs is found in elems by a user-provided comparison
||| @ p the comparison operator
||| @ elems the vector to search
||| @ xs what to search for
hasAnyBy : (p : a -> a -> Bool) -> (elems : Vect m a) -> (xs : Vect n a) -> Bool
hasAnyBy p elems []      = False
hasAnyBy p elems (x::xs) with (elemBy p x elems)
  | True  = True
  | False = hasAnyBy p elems xs

||| Check if any element of xs is found in elems using the default Boolean equality test
hasAny : Eq a => Vect m a -> Vect n a -> Bool
hasAny = hasAnyBy (==)

--------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------

||| Find the first element of the vector that satisfies some test
||| @ p the test to satisfy
find : (p : a -> Bool) -> (xs : Vect n a) -> Maybe a
find p []      = Nothing
find p (x::xs) with (p x)
  | True  = Just x
  | False = find p xs

||| Find the index of the first element of the vector that satisfies some test
findIndex : (a -> Bool) -> Vect n a -> Maybe Nat
findIndex = findIndex' 0
  where
    findIndex' : Nat -> (a -> Bool) -> Vect n a -> Maybe Nat
    findIndex' cnt p []      = Nothing
    findIndex' cnt p (x::xs) with (p x)
      | True  = Just cnt
      | False = findIndex' (S cnt) p xs

||| Find the indices of all elements that satisfy some test
total findIndices : (a -> Bool) -> Vect m a -> (p ** Vect p Nat)
findIndices = findIndices' 0
  where
    total findIndices' : Nat -> (a -> Bool) -> Vect m a -> (p ** Vect p Nat)
    findIndices' cnt p []      = (_ ** [])
    findIndices' cnt p (x::xs) with (findIndices' (S cnt) p xs)
      | (_ ** tail) =
       if p x then
        (_ ** cnt::tail)
       else
        (_ ** tail)

elemIndexBy : (a -> a -> Bool) -> a -> Vect m a -> Maybe Nat
elemIndexBy p e = findIndex $ p e

elemIndex : Eq a => a -> Vect m a -> Maybe Nat
elemIndex = elemIndexBy (==)

total elemIndicesBy : (a -> a -> Bool) -> a -> Vect m a -> (p ** Vect p Nat)
elemIndicesBy p e = findIndices $ p e

total elemIndices : Eq a => a -> Vect m a -> (p ** Vect p Nat)
elemIndices = elemIndicesBy (==)

--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------

||| Find all elements of a vector that satisfy some test
total filter : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter p [] = ( _ ** [] )
filter p (x::xs) with (filter p xs)
  | (_ ** tail) =
    if p x then
      (_ ** x::tail)
    else
      (_ ** tail)

||| Make the elements of some vector unique by some test
nubBy : (a -> a -> Bool) -> Vect n a -> (p ** Vect p a)
nubBy = nubBy' []
  where
    nubBy' : Vect m a -> (a -> a -> Bool) -> Vect n a -> (p ** Vect p a)
    nubBy' acc p []      = (_ ** [])
    nubBy' acc p (x::xs) with (elemBy p x acc)
      | True  = nubBy' acc p xs
      | False with (nubBy' (x::acc) p xs)
        | (_ ** tail) = (_ ** x::tail)

||| Make the elements of some vector unique by the default Boolean equality
nub : Eq a => Vect n a -> (p ** Vect p a)
nub = nubBy (==)

deleteBy : (a -> a -> Bool) -> a -> Vect n a -> (p ** Vect p a)
deleteBy _  _ []      = (_ ** [])
deleteBy eq x (y::ys) =
  let (len ** zs) = deleteBy eq x ys
  in if x `eq` y then (_ ** ys) else (S len ** y ::zs)

delete : (Eq a) => a -> Vect n a -> (p ** Vect p a)
delete = deleteBy (==)

--------------------------------------------------------------------------------
-- Splitting and breaking lists
--------------------------------------------------------------------------------

||| A tuple where the first element is a Vect of the n first elements and
||| the second element is a Vect of the remaining elements of the original Vect
||| It is equivalent to (take n xs, drop n xs)
||| @ m   the index to split at
||| @ xs  the Vect to split in two
splitAt : (n : Nat) -> (xs : Vect (n + m) a) -> (Vect n a, Vect m a)
splitAt n xs = (take n xs, drop n xs)

partition : (a -> Bool) -> Vect n a -> ((p ** Vect p a), (q ** Vect q a))
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

isPrefixOfBy : (a -> a -> Bool) -> Vect m a -> Vect n a -> Bool
isPrefixOfBy p [] right        = True
isPrefixOfBy p left []         = False
isPrefixOfBy p (x::xs) (y::ys) with (p x y)
  | True  = isPrefixOfBy p xs ys
  | False = False

isPrefixOf : Eq a => Vect m a -> Vect n a -> Bool
isPrefixOf = isPrefixOfBy (==)

isSuffixOfBy : (a -> a -> Bool) -> Vect m a -> Vect n a -> Bool
isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)

isSuffixOf : Eq a => Vect m a -> Vect n a -> Bool
isSuffixOf = isSuffixOfBy (==)

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

total maybeToVect : Maybe a -> (p ** Vect p a)
maybeToVect Nothing  = (_ ** [])
maybeToVect (Just j) = (_ ** [j])

total vectToMaybe : Vect n a -> Maybe a
vectToMaybe []      = Nothing
vectToMaybe (x::xs) = Just x

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

catMaybes : Vect n (Maybe a) -> (p ** Vect p a)
catMaybes []             = (_ ** [])
catMaybes (Nothing::xs)  = catMaybes xs
catMaybes ((Just j)::xs) with (catMaybes xs)
  | (_ ** tail) = (_ ** j::tail)

diag : Vect n (Vect n a) -> Vect n a
diag []             = []
diag ((x::xs)::xss) = x :: diag (map tail xss)

range : Vect n (Fin n)
range {n=Z}   = []
range {n=S _} = FZ :: map FS range

||| Transpose a Vect of Vects, turning rows into columns and vice versa.
|||
||| As the types ensure rectangularity, this is an involution, unlike `Prelude.List.transpose`.
transpose : Vect m (Vect n a) -> Vect n (Vect m a)
transpose []        = replicate _ []
transpose (x :: xs) = zipWith (::) x (transpose xs)

--------------------------------------------------------------------------------
-- Applicative/Monad/Traversable
--------------------------------------------------------------------------------

instance Applicative (Vect k) where
    pure = replicate _

    fs <$> vs = zipWith apply fs vs

instance Monad (Vect n) where
    m >>= f = diag (map f m)

instance Traversable (Vect n) where
    traverse f [] = pure Vect.Nil
    traverse f (x::xs) = [| Vect.(::) (f x) (traverse f xs) |]

--------------------------------------------------------------------------------
-- Show 
--------------------------------------------------------------------------------

instance Show a => Show (Vect n a) where
    show = show . toList

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

vectConsCong : (x : a) -> (xs : Vect n a) -> (ys : Vect m a) -> (xs = ys) -> (x :: xs = x :: ys)
vectConsCong x xs xs Refl = Refl

vectNilRightNeutral : (xs : Vect n a) -> xs ++ [] = xs
vectNilRightNeutral [] = Refl
vectNilRightNeutral (x :: xs) =
  vectConsCong _ _ _ (vectNilRightNeutral xs)

vectAppendAssociative : (x : Vect xLen a) -> (y : Vect yLen a) -> (z : Vect zLen a) -> x ++ (y ++ z) = (x ++ y) ++ z
vectAppendAssociative [] y z = Refl
vectAppendAssociative (x :: xs) ys zs =
  vectConsCong _ _ _ (vectAppendAssociative xs ys zs)

}

--------------------------------------------------------------------------------
-- DecEq
--------------------------------------------------------------------------------

total
vectInjective1 : {xs, ys : Vect n a} -> {x, y : a} -> x :: xs = y :: ys -> x = y
vectInjective1 {x=x} {y=x} {xs=xs} {ys=xs} Refl = Refl

total
vectInjective2 : {xs, ys : Vect n a} -> {x, y : a} -> x :: xs = y :: ys -> xs = ys
vectInjective2 {x=x} {y=x} {xs=xs} {ys=xs} Refl = Refl

instance DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (x :: ys)   | Yes Refl with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | Yes Refl | Yes Refl = Yes Refl
      decEq (x :: xs) (x :: ys) | Yes Refl | No  neq  = No (neq . vectInjective2)
    decEq (x :: xs) (y :: ys)   | No  neq             = No (neq . vectInjective1)

{- The following definition is elaborated in a wrong case-tree. Examination pending.
instance DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) with (decEq x y, decEq xs ys)
    decEq (x :: xs) (x :: xs) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (x :: xs) (y :: ys) | (_, No nEqTl) = No (\p => nEqTl (vectInjective2 p))
    decEq (x :: xs) (y :: ys) | (No nEqHd, _) = No (\p => nEqHd (vectInjective1 p))
-}

-- For the primitives, we have to cheat because we don't have access to their
-- internal implementations.


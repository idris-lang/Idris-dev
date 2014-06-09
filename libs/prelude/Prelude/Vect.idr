module Prelude.Vect

import Prelude.Fin
import Prelude.Foldable
import Prelude.Functor
import Prelude.List
import Prelude.Classes
import Prelude.Nat
import Prelude.Bool
import Prelude.Uninhabited

%access public
%default total

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
lengthCorrect Z [] = refl
lengthCorrect (S n) (x :: xs) = rewrite lengthCorrect n xs in refl

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
index fZ     (x::xs) = x
index (fS k) (x::xs) = index k xs
index fZ     [] impossible

||| Insert an element at a particular index
insertAt : Fin (S n) -> a -> Vect n a -> Vect (S n) a
insertAt fZ     y xs      = y :: xs
insertAt (fS k) y (x::xs) = x :: insertAt k y xs
insertAt (fS k) y []      = absurd k

||| Construct a new vector consisting of all but the indicated element
deleteAt : Fin (S n) -> Vect (S n) a -> Vect n a
deleteAt           fZ     (x::xs) = xs
deleteAt {n = S m} (fS k) (x::xs) = x :: deleteAt k xs
deleteAt {n = Z}   (fS k) (x::xs) = absurd k
deleteAt           _      [] impossible

||| Replace an element at a particlar index with another
replaceAt : Fin n -> t -> Vect n t -> Vect n t
replaceAt fZ     y (x::xs) = y :: xs
replaceAt (fS k) y (x::xs) = x :: replaceAt k y xs

||| Replace the element at a particular index with the result of applying a function to it
||| @ i the index to replace at
||| @ f the update function
||| @ xs the vector to replace in
updateAt : (i : Fin n) -> (f : t -> t) -> (xs : Vect n t) -> Vect n t
updateAt fZ     f (x::xs) = f x :: xs
updateAt (fS k) f (x::xs) = x :: updateAt k f xs

--------------------------------------------------------------------------------
-- Subvectors
--------------------------------------------------------------------------------

||| Get the first m elements of a Vect
||| @ m the number of elements to take
take : {n : Nat} -> (m : Fin (S n)) -> Vect n a -> Vect (cast m) a
take (fS k) []      = FinZElim k
take fZ     _       = []
take (fS k) (x::xs) = x :: take k xs

||| Remove the first m elements of a Vect
||| @ m the number of elements to remove
drop : (m : Fin (S n)) -> Vect n a -> Vect (n - cast m) a
drop (fS k) []      = FinZElim k
drop fZ     xs      ?= xs
drop (fS k) (x::xs) = drop k xs

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

||| Reverse the order of the elements of a vector
total reverse : {n : Nat} -> Vect n a -> Vect n a
reverse {n} xs = reverse' [] (plusZeroRightNeutral n) xs
  where
    total reverse' : {m, j, l : Nat} ->
                     Vect m a -> (j + m = l) -> Vect j a -> Vect l a
    reverse' {m} {j = Z  } {l} acc prf []      ?= acc
    reverse' {m} {j = S k} {l} acc prf (x::xs)  =
      let prf1 : (m + (S k) = l) = rewrite plusCommutative m (S k) in prf in
      let prf2 : (S (m + k) = l) = rewrite plusSuccRightSucc m k in prf1 in
      let prf3 : (S (k + m) = l) = rewrite plusCommutative k m in prf2 in
      let prf4 : (k + (S m) = l) = rewrite sym $ plusSuccRightSucc k m in prf3 in
      reverse' (x::acc) prf4 xs

||| Alternate an element between the other elements of a vector
||| @ sep the element to intersperse
||| @ xs the vector to separate with `sep`
intersperse : (sep : a) -> (xs : Vect n a) -> Vect (n + pred n) a
intersperse sep []      = []
intersperse sep (x::xs) = x :: intersperse' sep xs
  where
    intersperse' : a -> Vect n a -> Vect (n + n) a
    intersperse' sep []      = []
    intersperse' sep (x::xs) ?= sep :: x :: intersperse' sep xs

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

||| Combine two equal-length vectors pairwise
zip : Vect n a -> Vect n b -> Vect n (a, b)
zip = zipWith (\x => \y => (x,y))

||| Convert a vector of pairs to a pair of vectors
unzip : Vect n (a, b) -> (Vect n a, Vect n b)
unzip []           = ([], [])
unzip ((l, r)::xs) with (unzip xs)
  | (lefts, rights) = (l::lefts, r::rights)

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
  compare [] [] = EQ
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

-- XXX: causes Idris to enter an infinite loop when type checking in the REPL
--mapMaybe : (a -> Maybe b) -> Vect n a -> (p ** Vect b p)
--mapMaybe f []      = (_ ** [])
--mapMaybe f (x::xs) = mapMaybe' (f x)
-- XXX: working around the type restrictions on case statements
--  where
--    mapMaybe' : (Maybe b) -> (n ** Vect b n) -> (p ** Vect b p)
--    mapMaybe' Nothing  (n ** tail) = (n   ** tail)
--    mapMaybe' (Just j) (n ** tail) = (S n ** j::tail)

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

--------------------------------------------------------------------------------
-- Splitting and breaking lists
--------------------------------------------------------------------------------

||| A tuple where the first element is a Vect of the n first elements and
||| the second element is a Vect of the remaining elements of the original Vect
||| It is equivalent to (take n xs, drop n xs)
||| @ m   the index to split at
||| @ xs  the Vect to split in two
splitAt : {n : Nat} -> (m : Fin (S n)) -> (xs : Vect n a) -> (Vect (cast m) a, Vect (n - cast m) a)
splitAt n xs = (take n xs, drop n xs)

tails : Vect m a -> Vect m (Vect n a)
tails xs = xs :: case xs of
  []        => []
  _ :: xs'  => tails xs'

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

isInfixOf : Eq a => Vect m a -> Vect n a -> Bool
isInfixOf n h = any (isPrefixOf n) (with Vect tails h)

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
diag [] = []
diag ((x::xs)::xss) = x :: diag (map tail xss)

range : Vect n (Fin n)
range {n=Z} = []
range {n=S _} = fZ :: map fS range

||| Transpose a Vect of Vects, turning rows into columns and vice versa.
|||
||| As the types ensure rectangularity, this is an involution, unlike `Prelude.List.transpose`.
transpose : Vect m (Vect n a) -> Vect n (Vect m a)
transpose [] = replicate _ []
transpose (x :: xs) = zipWith (::) x (transpose xs)

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

vectConsCong : (x : a) -> (xs : Vect n a) -> (ys : Vect m a) -> (xs = ys) -> (x :: xs = x :: ys)
vectConsCong x xs xs refl = refl

vectNilRightNeutral : (xs : Vect n a) -> xs ++ [] = xs
vectNilRightNeutral [] = refl
vectNilRightNeutral (x :: xs) =
  vectConsCong _ _ _ (vectNilRightNeutral xs)

vectAppendAssociative : (x : Vect xLen a) -> (y : Vect yLen a) -> (z : Vect zLen a) -> x ++ (y ++ z) = (x ++ y) ++ z
vectAppendAssociative [] y z = refl
vectAppendAssociative (x :: xs) ys zs =
  vectConsCong _ _ _ (vectAppendAssociative xs ys zs)


--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

Prelude.Vect.drop_lemma_1 = proof {
  intros;
  rewrite sym (minusZeroRight n);
  trivial;
}

Prelude.Vect.reverse'_lemma_1 = proof {
    intros;
    rewrite prf;
    rewrite sym (plusZeroRightNeutral m);
    exact value;
}

Prelude.Vect.intersperse'_lemma_1 = proof {
  intros;
  rewrite (plusSuccRightSucc n1 n1);
  trivial;
}

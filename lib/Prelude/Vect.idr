module Prelude.Vect

import Prelude.Fin
import Prelude.List
import Prelude.Nat

%access public
%default total

infixr 7 :: 

data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a

--------------------------------------------------------------------------------
-- Indexing into vectors
--------------------------------------------------------------------------------

tail : Vect (S n) a -> Vect n a
tail (x::xs) = xs

head : Vect (S n) a -> a
head (x::xs) = x

last : Vect (S n) a -> a
last (x::[])    = x
last (x::y::ys) = last $ y::ys

init : Vect (S n) a -> Vect n a
init (x::[])    = []
init (x::y::ys) = x :: init (y::ys)

index : Fin n -> Vect n a -> a
index fZ     (x::xs) = x
index (fS k) (x::xs) = index k xs
index fZ     [] impossible

deleteAt : Fin (S n) -> Vect (S n) a -> Vect n a
deleteAt           fZ     (x::xs) = xs
deleteAt {n = S m} (fS k) (x::xs) = x :: deleteAt k xs
deleteAt           _      [] impossible

replaceAt : Fin n -> t -> Vect n t -> Vect n t
replaceAt fZ y (x::xs) = y::xs
replaceAt (fS k) y (x::xs) = x :: replaceAt k y xs

--------------------------------------------------------------------------------
-- Subvectors
--------------------------------------------------------------------------------

take : Fin n -> Vect n a -> (p ** Vect p a)
take fZ     xs      = (_ ** [])
take (fS k) []      impossible
take (fS k) (x::xs) with (take k xs)
  | (_ ** tail) = (_ ** x::tail)

drop : Fin n -> Vect n a -> (p ** Vect p a)
drop fZ     xs      = (_ ** xs)
drop (fS k) []      impossible
drop (fS k) (x::xs) = drop k xs

--------------------------------------------------------------------------------
-- Conversions to and from list
--------------------------------------------------------------------------------

toList : Vect n a -> List a
toList []      = []
toList (x::xs) = x :: toList xs

fromList : (l : List a) -> Vect (length l) a
fromList []      = []
fromList (x::xs) = x :: fromList xs

--------------------------------------------------------------------------------
-- Building (bigger) vectors
--------------------------------------------------------------------------------

(++) : Vect m a -> Vect n a -> Vect (m + n) a
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys

replicate : (n : Nat) -> a -> Vect n a
replicate Z     x = []
replicate (S k) x = x :: replicate k x

--------------------------------------------------------------------------------
-- Zips and unzips
--------------------------------------------------------------------------------

zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f []      []      = []
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

zip : Vect n a -> Vect n b -> Vect n (a, b)
zip = zipWith (\x => \y => (x,y))

unzip : Vect n (a, b) -> (Vect n a, Vect n b)
unzip []           = ([], [])
unzip ((l, r)::xs) with (unzip xs)
  | (lefts, rights) = (l::lefts, r::rights)

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

total foldl : (a -> b -> a) -> a -> Vect m b -> a
foldl f e []      = e
foldl f e (x::xs) = foldl f (f e x) xs

total foldr : (a -> b -> b) -> b -> Vect m a -> b
foldr f e []      = e
foldr f e (x::xs) = f x (foldr f e xs)

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

concat : Vect m (Vect n a) -> Vect (m * n) a
concat []      = []
concat (v::vs) = v ++ concat vs

total and : Vect m Bool -> Bool
and = foldr (&&) True

total or : Vect m Bool -> Bool
or = foldr (||) False

total any : (a -> Bool) -> Vect m a -> Bool
any p = Vect.or . map p

total all : (a -> Bool) -> Vect m a -> Bool
all p = Vect.and . map p

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

total reverse : Vect n a -> Vect n a
reverse = reverse' []
  where
    total reverse' : Vect m a -> Vect n a -> Vect (m + n) a
    reverse' acc []      ?= acc
    reverse' acc (x::xs) ?= reverse' (x::acc) xs

total intersperse' : a -> Vect m a -> (p ** Vect p a)
intersperse' sep []      = (_ ** [])
intersperse' sep (y::ys) with (intersperse' sep ys)
  | (_ ** tail) = (_ ** sep::y::tail)

total intersperse : a -> Vect m a -> (p ** Vect p a)
intersperse sep []      = (_ ** [])
intersperse sep (x::xs) with (intersperse' sep xs)
  | (_ ** tail) = (_ ** x::tail)

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

elemBy : (a -> a -> Bool) -> a -> Vect n a -> Bool
elemBy p e []      = False
elemBy p e (x::xs) with (p e x)
  | True  = True
  | False = elemBy p e xs

elem : Eq a => a -> Vect n a -> Bool
elem = elemBy (==)

lookupBy : (a -> a -> Bool) -> a -> Vect n (a, b) -> Maybe b
lookupBy p e []           = Nothing
lookupBy p e ((l, r)::xs) with (p e l)
  | True  = Just r
  | False = lookupBy p e xs

lookup : Eq a => a -> Vect n (a, b) -> Maybe b
lookup = lookupBy (==)

hasAnyBy : (a -> a -> Bool) -> Vect m a -> Vect n a -> Bool
hasAnyBy p elems []      = False
hasAnyBy p elems (x::xs) with (elemBy p x elems)
  | True  = True
  | False = hasAnyBy p elems xs

hasAny : Eq a => Vect m a -> Vect n a -> Bool
hasAny = hasAnyBy (==)

--------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------

find : (a -> Bool) -> Vect n a -> Maybe a
find p []      = Nothing
find p (x::xs) with (p x)
  | True  = Just x
  | False = find p xs

findIndex : (a -> Bool) -> Vect n a -> Maybe Nat
findIndex = findIndex' 0
  where
    findIndex' : Nat -> (a -> Bool) -> Vect n a -> Maybe Nat
    findIndex' cnt p []      = Nothing
    findIndex' cnt p (x::xs) with (p x)
      | True  = Just cnt
      | False = findIndex' (S cnt) p xs

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

total filter : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter p [] = ( _ ** [] )
filter p (x::xs) with (filter p xs)
  | (_ ** tail) =
    if p x then
      (_ ** x::tail)
    else
      (_ ** tail)

nubBy : (a -> a -> Bool) -> Vect n a -> (p ** Vect p a)
nubBy = nubBy' []
  where
    nubBy' : Vect m a -> (a -> a -> Bool) -> Vect n a -> (p ** Vect p a)
    nubBy' acc p []      = (_ ** [])
    nubBy' acc p (x::xs) with (elemBy p x acc)
      | True  = nubBy' acc p xs
      | False with (nubBy' (x::acc) p xs)
        | (_ ** tail) = (_ ** x::tail)

nub : Eq a => Vect n a -> (p ** Vect p a)
nub = nubBy (==)

--------------------------------------------------------------------------------
-- Splitting and breaking lists
--------------------------------------------------------------------------------

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
diag [] = []
diag ((x::xs)::xss) = x :: diag (map tail xss)

range : Vect n (Fin n)
range =
  reverse range_
 where
  range_ : Vect n (Fin n)
  range_ {n=Z} = Nil
  range_ {n=(S _)} = last :: map weaken range_

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

Prelude.Vect.reverse'_lemma_2 = proof {
    intros;
    rewrite (plusSuccRightSucc m n1);
    exact value;
}

Prelude.Vect.reverse'_lemma_1 = proof {
    intros;
    rewrite sym (plusZeroRightNeutral m);
    exact value;
}


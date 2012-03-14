module prelude.vect

import prelude.fin
import prelude.list
import prelude.nat

%access public

infixr 7 :: 

data Vect : Set -> Nat -> Set where
  Nil  : Vect a O
  (::) : a -> Vect a n -> Vect a (S n)

--------------------------------------------------------------------------------
-- Indexing into vectors
--------------------------------------------------------------------------------

tail : Vect a (S n) -> Vect a n
tail (x::xs) = xs

head : Vect a (S n) -> a
head (x::xs) = x

last : Vect a (S n) -> a
last (x::[])    = x
last (x::y::ys) = last $ y::ys

init : Vect a (S n) -> Vect a n
init (x::[])    = []
init (x::y::ys) = x :: init (y::ys)

index : Fin n -> Vect a n -> a
index fO     (x::xs) = x
index (fS k) (x::xs) = index k xs
index fO     [] impossible
index (fS _) [] impossible

--------------------------------------------------------------------------------
-- Subvectors
--------------------------------------------------------------------------------

take : Fin n -> Vect a n -> (p ** Vect a p)
take fO     xs      = (_ ** [])
take (fS k) []      impossible
take (fS k) (x::xs) with (take k xs)
  | (_ ** tail) = (_ ** x::tail)

drop : Fin n -> Vect a n -> (p ** Vect a p)
drop fO     xs      = (_ ** xs)
drop (fS k) []      impossible
drop (fS k) (x::xs) = drop k xs

--------------------------------------------------------------------------------
-- Conversions to and from list
--------------------------------------------------------------------------------

total toList : Vect a n -> List a
toList []      = []
toList (x::xs) = x :: toList xs

total fromList : (l : List a) -> Vect a (length l)
fromList []      = []
fromList (x::xs) = x :: fromList xs

--------------------------------------------------------------------------------
-- Building bigger vectors
--------------------------------------------------------------------------------

total
(++) : Vect a m -> Vect a n -> Vect a (m + n)
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys

--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

total map : (a -> b) -> Vect a n -> Vect b n
map f []        = []
map f (x::xs) = f x :: map f xs

-- XXX: causes Idris to enter an infinite loop when type checking in the REPL
--mapMaybe : (a -> Maybe b) -> Vect a n -> (p ** Vect b p)
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

total foldl : (a -> b -> a) -> a -> Vect b m -> a
foldl f e []      = e
foldl f e (x::xs) = foldl f (f e x) xs

total foldr : (a -> b -> b) -> b -> Vect a m -> b
foldr f e []      = e
foldr f e (x::xs) = f x (foldr f e xs)

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

total and : Vect Bool m -> Bool
and = foldr (&&) True

total or : Vect Bool m -> Bool
or = foldr (||) False

total any : (a -> Bool) -> Vect a m -> Bool
any p = or . map p

total all : (a -> Bool) -> Vect a m -> Bool
all p = and . map p

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

total reverse : Vect a n -> Vect a n
reverse = reverse' []
  where
    total reverse' : Vect a m -> Vect a n -> Vect a (m + n)
    reverse' acc []      ?= acc
    reverse' acc (x::xs) ?= reverse' (x::acc) xs

total intersperse' : a -> Vect a m -> (p ** Vect a p)
intersperse' sep []      = (_ ** [])
intersperse' sep (y::ys) with (intersperse' sep ys)
  | (_ ** tail) = (_ ** sep::y::tail)

total intersperse : a -> Vect a m -> (p ** Vect a p)
intersperse sep []      = (_ ** [])
intersperse sep (x::xs) with (intersperse' sep xs)
  | (_ ** tail) = (_ ** x::tail)

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

elemBy : (a -> a -> Bool) -> a -> Vect a n -> Bool
elemBy p e []      = False
elemBy p e (x::xs) with (p e x)
  | True  = True
  | False = elemBy p e xs

elem : Eq a => a -> Vect a n -> Bool
elem = elemBy (==)

lookupBy : (a -> a -> Bool) -> a -> Vect (a, b) n -> Maybe b
lookupBy p e []           = Nothing
lookupBy p e ((l, r)::xs) with (p e l)
  | True  = Just r
  | False = lookupBy p e xs

lookup : Eq a => a -> Vect (a, b) n -> Maybe b
lookup = lookupBy (==)

hasAnyBy : (a -> a -> Bool) -> Vect a m -> Vect a n -> Bool
hasAnyBy p elems []      = False
hasAnyBy p elems (x::xs) with (elemBy p x elems)
  | True  = True
  | False = hasAnyBy p elems xs

hasAny : Eq a => Vect a m -> Vect a n -> Bool
hasAny = hasAnyBy (==)

--------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------

find : (a -> Bool) -> Vect a n -> Maybe a
find p []      = Nothing
find p (x::xs) with (p x)
  | True  = Just x
  | False = find p xs

findIndex : (a -> Bool) -> Vect a n -> Maybe Nat
findIndex = findIndex' 0
  where
    findIndex' : Nat -> (a -> Bool) -> Vect a n -> Maybe Nat
    findIndex' cnt p []      = Nothing
    findIndex' cnt p (x::xs) with (p x)
      | True  = Just cnt
      | False = findIndex' (S cnt) p xs

total findIndices : (a -> Bool) -> Vect a m -> (p ** Vect Nat p)
findIndices = findIndices' 0
  where
    total findIndices' : Nat -> (a -> Bool) -> Vect a m -> (p ** Vect Nat p)
    findIndices' cnt p []      = (_ ** [])
    findIndices' cnt p (x::xs) with (findIndices' (S cnt) p xs)
      | (_ ** tail) =
       if p x then
        (_ ** cnt::tail)
       else
        (_ ** tail)

elemIndexBy : (a -> a -> Bool) -> a -> Vect a m -> Maybe Nat
elemIndexBy p e = findIndex $ p e

elemIndex : Eq a => a -> Vect a m -> Maybe Nat
elemIndex = elemIndexBy (==)

total elemIndicesBy : (a -> a -> Bool) -> a -> Vect a m -> (p ** Vect Nat p)
elemIndicesBy p e = findIndices $ p e

total elemIndices : Eq a => a -> Vect a m -> (p ** Vect Nat p)
elemIndices = elemIndicesBy (==)

--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------

total filter : (a -> Bool) -> Vect a n -> (p ** Vect a p)
filter p [] = ( _ ** [] )
filter p (x::xs) with (filter p xs)
  | (_ ** tail) =
    if p x then
      (_ ** x::tail)
    else
      (_ ** tail)

nubBy : (a -> a -> Bool) -> Vect a n -> (p ** Vect a p)
nubBy = nubBy' []
  where
    nubBy' : Vect a m -> (a -> a -> Bool) -> Vect a n -> (p ** Vect a p)
    nubBy' acc p []      = (_ ** [])
    nubBy' acc p (x::xs) with (elemBy p x acc)
      | True  = nubBy' acc p xs
      | False with (nubBy' (x::acc) p xs)
        | (_ ** tail) = (_ ** x::tail)

nub : Eq a => Vect a n -> (p ** Vect a p)
nub = nubBy (==)

--------------------------------------------------------------------------------
-- Splitting and breaking lists
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

isPrefixOfBy : (a -> a -> Bool) -> Vect a m -> Vect a n -> Bool
isPrefixOfBy p [] right        = True
isPrefixOfBy p left []         = False
isPrefixOfBy p (x::xs) (y::ys) with (p x y)
  | True  = isPrefixOfBy p xs ys
  | False = False

isPrefixOf : Eq a => Vect a m -> Vect a n -> Bool
isPrefixOf = isPrefixOfBy (==)

isSuffixOfBy : (a -> a -> Bool) -> Vect a m -> Vect a n -> Bool
isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)

isSuffixOf : Eq a => Vect a m -> Vect a n -> Bool
isSuffixOf = isSuffixOfBy (==)

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

total maybeToVect : Maybe a -> (p ** Vect a p)
maybeToVect Nothing  = (_ ** [])
maybeToVect (Just j) = (_ ** [j])

total vectToMaybe : Vect a n -> Maybe a
vectToMaybe []      = Nothing
vectToMaybe (x::xs) = Just x

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

catMaybes : Vect (Maybe a) n -> (p ** Vect a p)
catMaybes []             = (_ ** [])
catMaybes (Nothing::xs)  = catMaybes xs
catMaybes ((Just j)::xs) with (catMaybes xs)
  | (_ ** tail) = (_ ** j::tail)

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

prelude.vect.reverse'_lemma_2 = proof {
    intros;
    rewrite (plusSuccRightSucc m n1);
    exact value;
}

prelude.vect.reverse'_lemma_1 = proof {
    intros;
    rewrite sym (plusZeroRightNeutral m);
    exact value;
}


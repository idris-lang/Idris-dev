module prelude.vect

import prelude.fin
import prelude.list
import prelude.nat

%access public

infixr 10 :: 

data Vect : Set -> Nat -> Set where
  Nil  : Vect a O
  (::) : a -> Vect a n -> Vect a (S n)

--------------------------------------------------------------------------------
-- Indexing into vectors
--------------------------------------------------------------------------------

tail : Vect a (S n) -> Vect a n
tail (x::xs) = xs
tail [] impossible

head : Vect a (S n) -> a
head (x::xs) = x
head [] impossible

last : Vect a (S n) -> a
last [] impossible
last (x::[])    = x
last (x::y::ys) = last $ y::ys

init : Vect a (S n) -> Vect a n
init [] impossible
init (x::[])    = []
init (x::y::ys) = x :: init (y::ys)

index : Fin n -> Vect a n -> a
index fO     (x::xs) = x
index (fS k) (x::xs) = index k xs
index fO     [] impossible
index (fS _) [] impossible

--------------------------------------------------------------------------------
-- Conversions to and from list
--------------------------------------------------------------------------------

toList : Vect a n -> List a
toList []      = []
toList (x::xs) = x :: toList xs

fromList : (l : List a) -> Vect a (length l)
fromList []      = []
fromList (x::xs) = x :: fromList xs

--------------------------------------------------------------------------------
-- Building bigger vectors
--------------------------------------------------------------------------------

(++) : Vect a m -> Vect a n -> Vect a (m + n)
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

reverse : Vect a n -> Vect a n
reverse = reverse' []
  where
    reverse' : Vect a m -> Vect a n -> Vect a (m + n)
    reverse' acc []      ?= acc
    reverse' acc (x::xs) ?= reverse' (x::acc) xs

--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

map : (a -> b) -> Vect a n -> Vect b n
map f []        = []
map f (x::xs) = f x :: map f xs

--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------

filter : (a -> Bool) -> Vect a n -> (p ** Vect a p)
filter p [] = ( _ ** [] )
filter p (x::xs) with (filter p xs)
  | (_ ** tail) =
    if p x then
      (_ ** x::tail)
    else
      (_ ** tail)

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


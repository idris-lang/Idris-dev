module prelude.list

import builtins

import prelude.algebra
import prelude.maybe
import prelude.nat

%access public

infixr 7 :: 

data List a
  = Nil
  | (::) a (List a)

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

isNil : List a -> Bool
isNil []      = True
isNil (x::xs) = False

isCons : List a -> Bool
isCons []      = False
isCons (x::xs) = True

--------------------------------------------------------------------------------
-- Indexing into lists
--------------------------------------------------------------------------------

head : (l : List a) -> (isCons l = True) -> a
head (x::xs) p = x

head' : (l : List a) -> Maybe a
head' []      = Nothing
head' (x::xs) = Just x

tail : (l : List a) -> (isCons l = True) -> List a
tail (x::xs) p = xs

tail' : (l : List a) -> Maybe (List a)
tail' []      = Nothing
tail' (x::xs) = Just xs

last : (l : List a) -> (isCons l = True) -> a
last (x::xs) p =
  case xs of
    []    => x
    y::ys => last (y::ys) ?lastProof

last' : (l : List a) -> Maybe a
last' []      = Nothing
last' (x::xs) =
  case xs of
    []    => Just x
    y::ys => last' xs

init : (l : List a) -> (isCons l = True) -> List a
init (x::xs) p =
  case xs of
    []    => []
    y::ys => x :: init (y::ys) ?initProof

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

take : Nat -> List a -> List a
take O     xs      = []
take (S n) []      = []
take (S n) (x::xs) = x :: take n xs

drop : Nat -> List a -> List a
drop O     xs      = xs
drop (S n) []      = []
drop (S n) (x::xs) = drop n xs

--------------------------------------------------------------------------------
-- Misc.
--------------------------------------------------------------------------------

list : a -> (a -> List a -> a) -> List a -> a
list nil cons []      = nil
list nil cons (x::xs) = cons x xs

length : List a -> Nat
length []      = 0
length (x::xs) = 1 + length xs

--------------------------------------------------------------------------------
-- Building bigger lists
--------------------------------------------------------------------------------

(++) : List a -> List a -> List a
(++) [] right      = right
(++) (x::xs) right = x :: (xs ++ right)

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

-- XXX: unification failure
-- instance VerifiedSemigroup (List a) where
--  semigroupOpIsAssociative = appendAssociative

--------------------------------------------------------------------------------
-- Zips and unzips
--------------------------------------------------------------------------------

zipWith : (f : a -> b -> c) -> (l : List a) -> (r : List b) ->
  (length l = length r) -> List c
zipWith f []      []      p = []
zipWith f (x::xs) (y::ys) p = f x y :: (zipWith f xs ys ?zipWithTailProof)

zipWith3 : (f : a -> b -> c -> d) -> (x : List a) -> (y : List b) ->
  (z : List c) -> (length x = length y) -> (length y = length z) -> List d
zipWith3 f []      []      []      p q = []
zipWith3 f (x::xs) (y::ys) (z::zs) p q =
  f x y z :: (zipWith3 f xs ys zs ?zipWith3TailProof ?zipWith3TailProof')

zip : (l : List a) -> (r : List b) -> (length l = length r) -> List (a, b)
zip = zipWith (\x => \y => (x, y))

zip3 : (x : List a) -> (y : List b) -> (z : List c) -> (length x = length y) ->
  (length y = length z) -> List (a, b, c)
zip3 = zipWith3 (\x => \y => \z => (x, y, z))

unzip : List (a, b) -> (List a, List b)
unzip []           = ([], [])
unzip ((l, r)::xs) with (unzip xs)
  | (lefts, rights) = (l::lefts, r::rights)

unzip3 : List (a, b, c) -> (List a, List b, List c)
unzip3 []              = ([], [], [])
unzip3 ((l, c, r)::xs) with (unzip3 xs)
  | (lefts, centres, rights) = (l::lefts, c::centres, r::rights)

--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

map : (a -> b) -> List a -> List b
map f []      = []
map f (x::xs) = f x :: map f xs

mapMaybe : (a -> Maybe b) -> List a -> List b
mapMaybe f []      = []
mapMaybe f (x::xs) =
  case f x of
    Nothing => mapMaybe f xs
    Just j  => j :: mapMaybe f xs

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

foldl : (a -> b -> a) -> a -> List b -> a
foldl f e []      = e
foldl f e (x::xs) = foldl f (f e x) xs

foldr : (a -> b -> b) -> b -> List a -> b
foldr f e []      = e
foldr f e (x::xs) = f x (foldr f e xs)

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

mconcat : Monoid a => List a -> a
mconcat = foldr (<+>) neutral

concat : List (List a) -> List a
concat []      = []
concat (x::xs) = x ++ concat xs

concatMap : (a -> List b) -> List a -> List b
concatMap f []      = []
concatMap f (x::xs) = f x ++ concatMap f xs

and : List Bool -> Bool
and = foldr (&&) True

or : List Bool -> Bool
or = foldr (||) False

any : (a -> Bool) -> List a -> Bool
any p = or . map p

all : (a -> Bool) -> List a -> Bool
all p = and . map p

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

reverse : List a -> List a
reverse = reverse' []
  where
    reverse' : List a -> List a -> List a
    reverse' acc []      = acc
    reverse' acc (x::xs) = reverse' (x::acc) xs

intersperse : a -> List a -> List a
intersperse sep []      = []
intersperse sep (x::xs) = x :: intersperse' sep xs
  where
    intersperse' : a -> List a -> List a
    intersperse' sep []      = []
    intersperse' sep (y::ys) = sep :: y :: intersperse' sep ys

intercalate : List a -> List (List a) -> List a
intercalate sep l = concat $ intersperse sep l

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

elemBy : (a -> a -> Bool) -> a -> List a -> Bool
elemBy p e []      = False
elemBy p e (x::xs) =
  if p e x then
    True
  else
    elemBy p e xs

elem : Eq a => a -> List a -> Bool
elem = elemBy (==)

lookupBy : (a -> a -> Bool) -> a -> List (a, b) -> Maybe b
lookupBy p e []      = Nothing
lookupBy p e (x::xs) =
  let (l, r) = x in
    if p e l then
      Just r
    else
      lookupBy p e xs

lookup : Eq a => a -> List (a, b) -> Maybe b
lookup = lookupBy (==)

hasAnyBy : (a -> a -> Bool) -> List a -> List a -> Bool
hasAnyBy p elems []      = False
hasAnyBy p elems (x::xs) =
  if elemBy p x elems then
    True
  else
    hasAnyBy p elems xs

hasAny : Eq a => List a -> List a -> Bool
hasAny = hasAnyBy (==)

--------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------

find : (a -> Bool) -> List a -> Maybe a
find p []      = Nothing
find p (x::xs) =
  if p x then
    Just x
  else
    find p xs

findIndex : (a -> Bool) -> List a -> Maybe Nat
findIndex = findIndex' 0
  where
    findIndex' : Nat -> (a -> Bool) -> List a -> Maybe Nat
    findIndex' cnt p []      = Nothing
    findIndex' cnt p (x::xs) =
      if p x then
        Just cnt
      else
        findIndex' (S cnt) p xs

findIndices : (a -> Bool) -> List a -> List Nat
findIndices = findIndices' 0
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

filter : (a -> Bool) -> List a -> List a
filter p []      = []
filter p (x::xs) =
  if p x then
    x :: filter p xs
  else
    filter p xs

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

nub : Eq a => List a -> List a
nub = nubBy (==)

--------------------------------------------------------------------------------
-- Splitting and breaking lists
--------------------------------------------------------------------------------

span : (a -> Bool) -> List a -> (List a, List a)
span p []      = ([], [])
span p (x::xs) =
  if p x then
    let (ys, zs) = span p xs in
      (x::ys, zs)
  else
    ([], x::xs)

break : (a -> Bool) -> List a -> (List a, List a)
break p = span (not . p)

split : (a -> Bool) -> List a -> List (List a)
split p [] = []
split p xs =
  case break p xs of
    (chunk, [])          => [chunk]
    (chunk, (c :: rest)) => chunk :: split p rest

partition : (a -> Bool) -> List a -> (List a, List a)
partition p []      = ([], [])
partition p (x::xs) =
  let (lefts, rights) = partition p xs in
    if p x then
      (x::lefts, rights)
    else
      (lefts, x::rights)

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

isPrefixOf : Eq a => List a -> List a -> Bool
isPrefixOf = isPrefixOfBy (==)

isSuffixOfBy : (a -> a -> Bool) -> List a -> List a -> Bool
isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)

isSuffixOf : Eq a => List a -> List a -> Bool
isSuffixOf = isSuffixOfBy (==)

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
  case order x y of
    LT => x :: mergeBy order xs (y::ys)
    _  => y :: mergeBy order (x::xs) ys

merge : Ord a => List a -> List a -> List a
merge = mergeBy compare

sort : Ord a => List a -> List a
sort []  = []
sort [x] = [x]
sort xs  =
  let (x, y) = split xs in
    merge (sort x) (sort y)
  where
    splitRec : List a -> List a -> (List a -> List a) -> (List a, List a)
    splitRec (_::_::xs) (y::ys) zs = splitRec xs ys (zs . ((::) y))
    splitRec _          ys      zs = (zs [], ys)

    split : List a -> (List a, List a)
    split xs = splitRec xs xs id

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

maybeToList : Maybe a -> List a
maybeToList Nothing  = []
maybeToList (Just j) = [j]

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

-- append
appendNilRightNeutral : (l : List a) ->
  l ++ [] = l
appendNilRightNeutral []      = refl
appendNilRightNeutral (x::xs) =
  let inductiveHypothesis = appendNilRightNeutral xs in
    ?appendNilRightNeutralStepCase

appendAssociative : (l : List a) -> (c : List a) -> (r : List a) ->
  l ++ (c ++ r) = (l ++ c) ++ r
appendAssociative []      c r = refl
appendAssociative (x::xs) c r =
  let inductiveHypothesis = appendAssociative xs c r in
    ?appendAssociativeStepCase

-- length
lengthAppend : (left : List a) -> (right : List a) ->
  length (left ++ right) = length left + length right
lengthAppend []      right = refl
lengthAppend (x::xs) right =
  let inductiveHypothesis = lengthAppend xs right in
    ?lengthAppendStepCase

-- map
mapPreservesLength : (f : a -> b) -> (l : List a) ->
  length (map f l) = length l
mapPreservesLength f []      = refl
mapPreservesLength f (x::xs) =
  let inductiveHypothesis = mapPreservesLength f xs in
    ?mapPreservesLengthStepCase

mapDistributesOverAppend : (f : a -> b) -> (l : List a) -> (r : List a) ->
  map f (l ++ r) = map f l ++ map f r
mapDistributesOverAppend f []      r = refl
mapDistributesOverAppend f (x::xs) r =
  let inductiveHypothesis = mapDistributesOverAppend f xs r in
    ?mapDistributesOverAppendStepCase

mapFusion : (f : b -> c) -> (g : a -> b) -> (l : List a) ->
  map f (map g l) = map (f . g) l
mapFusion f g []      = refl
mapFusion f g (x::xs) =
  let inductiveHypothesis = mapFusion f g xs in
    ?mapFusionStepCase

-- hasAny
hasAnyByNilFalse : (p : a -> a -> Bool) -> (l : List a) ->
  hasAnyBy p [] l = False
hasAnyByNilFalse p []      = refl
hasAnyByNilFalse p (x::xs) =
  let inductiveHypothesis = hasAnyByNilFalse p xs in
    ?hasAnyByNilFalseStepCase

hasAnyNilFalse : Eq a => (l : List a) -> hasAny [] l = False
hasAnyNilFalse l = ?hasAnyNilFalseBody
    
--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

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

initProof = proof {
    intros;
    trivial;
}

lastProof = proof {
    intros;
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


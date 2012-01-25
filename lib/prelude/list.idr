module prelude.list

import prelude.maybe
import builtins

%access public

infixr 7 :: 

data List a = Nil | (::) a (List a)

rev : List a -> List a
rev xs = revAcc [] xs where
  revAcc : List a -> List a -> List a
  revAcc acc []        = acc
  revAcc acc (x :: xs) = revAcc (x :: acc) xs

app : List a -> List a -> List a
app []        xs = xs
app (x :: xs) ys = x :: app xs ys

head : List a -> Maybe a
head []        = Nothing
head (x :: xs) = Just x

tail : List a -> List a
tail []        = []
tail (x :: xs) = xs

length : List a -> Int
length []        = 0
length (x :: xs) = 1 + length xs

take : Int -> List a -> List a
take 0 xs = []
take n [] = []
take n (x :: xs) = x :: take (n-1) xs

drop : Int -> List a -> List a
drop 0 xs = xs
drop n [] = []
drop n (x :: xs) = drop (n-1) xs

map : (a -> b) -> List a -> List b
map f []        = []
map f (x :: xs) = f x :: map f xs

concatMap : (a -> List b) -> List a -> List b
concatMap f [] = []
concatMap f (x :: xs) = app (f x) (concatMap f xs)

mapMaybe : (a -> Maybe b) -> List a -> List b
mapMaybe f [] = []
mapMaybe f (x :: xs) = case f x of
                           Nothing => mapMaybe f xs
                           Just v  => v :: mapMaybe f xs

foldl : (a -> b -> a) -> a -> List b -> a
foldl f a []        = a
foldl f a (x :: xs) = foldl f (f a x) xs

foldr : (a -> b -> b) -> b -> List a -> b
foldr f b []        = b
foldr f b (x :: xs) = f x (foldr f b xs)

filter : (y -> Bool) -> List y -> List y
filter pred [] = []
filter pred (x :: xs) = if (pred x) then (x :: filter pred xs)
                                    else (filter pred xs)

elem : Eq a => a -> List a -> Bool
elem x [] = False
elem x (y :: ys) = if (x == y) then True else (elem x ys)

lookup : Eq k => k -> List (k, v) -> Maybe v
lookup k [] = Nothing
lookup k ((x, v) :: xs) = if (x == k) then (Just v) else (lookup k xs)

sort : Ord a => List a -> List a
sort []  = []
sort [x] = [x]
sort xs = let (x, y) = split xs in
              merge (sort x) (sort y) where
    splitrec : List a -> List a -> (List a -> List a) -> (List a, List a)
    splitrec (_ :: _ :: xs) (y :: ys) zs = splitrec xs ys (zs . ((::) y))
    splitrec _              ys        zs = (zs [], ys)

    split : List a -> (List a, List a)
    split xs = splitrec xs xs id

    merge : Ord a => List a -> List a -> List a
    merge xs        []        = xs
    merge []        ys        = ys
    merge (x :: xs) (y :: ys) = if (x < y) then (x :: merge xs (y :: ys))
                                           else (y :: merge (x :: xs) ys)

span : (a -> Bool) -> List a -> (List a, List a)
span p [] = ([], [])
span p (x :: xs) with (p x) 
   | True with (span p xs)
      | (ys, zs) = (x :: ys, zs)
   | False = ([], x :: xs)

break : (a -> Bool) -> List a -> (List a, List a)
break p = span (not . p)
  
split : (a -> Bool) -> List a -> List (List a)
split p [] = []
split p xs = case break p xs of
                  (chunk, []) => [chunk]
                  (chunk, (c :: rest)) => chunk :: split p rest

any : (a -> Bool) -> List a -> Bool
any predicate [] = False
any predicate (a::rest) =
  if predicate a
    then True
    else any predicate rest

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
-- Instances
--------------------------------------------------------------------------------

instance (Eq a) => Eq (List a) where
  (==) [] [] = True
  (==) (a::restA) (b::restB) =
    if a == b
      then restA == restB
      else False
  (==) _ _ = False


instance Ord a => Ord (List a) where
  compare [] [] = EQ
  compare [] _ = LT
  compare _ [] = GT
  compare (a::restA) (b::restB) =
    if a /= b
      then compare a b
      else compare restA restB

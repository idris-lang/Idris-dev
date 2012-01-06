module prelude.list

import prelude.maybe
import builtins

%access public

infixr 7 :: 

data List a = Nil | (::) a (List a)

rev : List a -> List a
rev xs = revAcc [] xs where {
  revAcc : List a -> List a -> List a
  revAcc acc [] = acc
  revAcc acc (x :: xs) = revAcc (x :: acc) xs
}

app : List a -> List a -> List a
app [] xs = xs
app (x :: xs) ys = x :: app xs ys

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
mapMaybe f (x :: xs) = case f x of {
                           Nothing => mapMaybe f xs
                         | Just v  => v :: mapMaybe f xs
                       }

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
              merge (sort x) (sort y) where {
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
}

span : (a -> Bool) -> List a -> (List a, List a)
span p [] = ([], [])
span p (x :: xs) with p x {
   | True with span p xs {
      | (ys, zs) = (x :: ys, zs)
   }
   | False = ([], x :: xs)
}

break : (a -> Bool) -> List a -> (List a, List a)
break p = span (not . p)
  
split : (a -> Bool) -> List a -> List (List a)
split p [] = []
split p xs = case break p xs of {
                  (chunk, []) => [chunk]
                | (chunk, (c :: rest)) => chunk :: split p rest
             }


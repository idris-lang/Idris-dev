module Prelude.Stream

import Builtins

import Prelude.Basics
import Prelude.Functor
import Prelude.Applicative
import Prelude.Monad
import Prelude.Nat
import Prelude.List

%access public
%default total

||| An infinite stream
codata Stream : Type -> Type where
  (::) : a -> Stream a -> Stream a

-- Hints for interactive editing
%name Stream xs,ys,zs,ws

instance Functor Stream where
    f <$> (x::xs) = f x :: map f xs

||| The first element of an infinite stream
head : Stream a -> a
head (x::xs) = x

||| All but the first element
tail : Stream a -> Stream a
tail (x::xs) = xs

||| Take precisely n elements from the stream
||| @ n how many elements to take
||| @ xs the stream
take : (n : Nat) -> (xs : Stream a) -> List a
take Z _ = []
take (S n) (x :: xs) = x :: (take n xs)

||| Drop the first n elements from the stream
||| @ n how many elements to drop
%assert_total
drop : (n : Nat) -> Stream a -> Stream a
drop Z     xs = xs
drop (S k) (x::xs) = drop k xs

||| An infinite stream of repetitions of the same thing
repeat : a -> Stream a
repeat x = x :: repeat x

||| Generate an infinite stream by repeatedly applying a function
||| @ f the function to iterate
||| @ x the initial value that will be the head of the stream
iterate : (f : a -> a) -> (x : a) -> Stream a
iterate f x = x :: iterate f (f x)

||| Get the nth element of a stream
index : Nat -> Stream a -> a
index Z     (x::xs) = x
index (S k) (x::xs) = index k xs

||| Combine two streams element-wise using a function
zipWith : (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

||| Combine three streams by applying a function element-wise along them
zipWith3 : (a -> b -> c -> d) -> Stream a -> Stream b -> Stream c -> Stream d
zipWith3 f (x::xs) (y::ys) (z::zs) = f x y z :: zipWith3 f xs ys zs

||| Create a stream of pairs from two streams
zip : Stream a -> Stream b -> Stream (a, b)
zip = zipWith (\x,y => (x,y))

||| Combine three streams into a stream of tuples elementwise
zip3 : Stream a -> Stream b -> Stream c -> Stream (a, b, c)
zip3 = zipWith3 (\x,y,z => (x,y,z))

||| Create a pair of streams from a stream of pairs
unzip : Stream (a, b) -> (Stream a, Stream b)
unzip xs = (map fst xs, map snd xs)

||| Split a stream of three-element tuples into three streams
unzip3 : Stream (a, b, c) -> (Stream a, Stream b, Stream c)
unzip3 xs = (map (\(x,_,_) => x) xs, map (\(_,x,_) => x) xs, map (\(_,_,x) => x) xs)

||| Return the diagonal elements of a stream of streams
diag : Stream (Stream a) -> Stream a
diag ((x::xs)::xss) = x :: diag (map tail xss)

||| Fold a Stream corecursively. Since there is no Nil, no initial value is used.
||| @ f the combining function
||| @ xs the Stream to fold up
partial -- the recursive call isn't guarded!
foldr : (f : a -> Inf b -> b) -> (xs : Stream a) -> b
foldr f (x :: xs) = f x (foldr f xs)

||| Produce a Stream of left folds of prefixes of the given Stream
||| @ f the combining function
||| @ acc the initial value
||| @ xs the Stream to process
scanl : (f : a -> b -> a) -> (acc : a) -> (xs : Stream b) -> Stream a
scanl f acc (x :: xs) = acc :: scanl f (f acc x) xs

||| Produce a Stream of (corecursive) right folds of tails of the given Stream
||| @ f the combining function
||| @ xs the Stream to fold up
-- Reusing the head of the corecursion in the obvious way doesn't productivity check
partial -- and the call to foldr isn't guarded anyway!
scanr : (f : a -> Inf b -> b) -> (xs : Stream a) -> Stream b
scanr f (x :: xs) = f x (foldr f xs) :: scanr f xs

instance Applicative Stream where
  pure = repeat
  (<*>) = zipWith apply

instance Monad Stream where
  s >>= f = diag (map f s)


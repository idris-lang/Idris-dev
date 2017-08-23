module Prelude.Stream

import Builtins

import Prelude.Basics
import Prelude.Functor
import Prelude.Applicative
import Prelude.Monad
import Prelude.Nat
import Prelude.List

%access public export
%default total

||| An infinite stream
data Stream : Type -> Type where
  (::) : (value : elem) -> Inf (Stream elem) -> Stream elem

-- Hints for interactive editing
%name Stream xs,ys,zs,ws

-- Usage hints for erasure analysis
%used Stream.(::) value

Functor Stream where
    map f (x::xs) = f x :: map f xs

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

||| Combine two streams element-wise using a function.
|||
||| @ f the function to combine elements with
||| @ xs the first stream of elements
||| @ ys the second stream of elements
zipWith : (f : a -> b -> c) -> (xs : Stream a) -> (ys : Stream b) -> Stream c
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

||| Produce a Stream of left folds of prefixes of the given Stream
||| @ f the combining function
||| @ acc the initial value
||| @ xs the Stream to process
scanl : (f : a -> b -> a) -> (acc : a) -> (xs : Stream b) -> Stream a
scanl f acc (x :: xs) = acc :: scanl f (f acc x) xs

||| Produce a Stream repeating a sequence
||| @ xs the sequence to repeat
||| @ ok proof that the list is non-empty
cycle : (xs : List a) -> {auto ok : NonEmpty xs} -> Stream a
cycle {a} (x :: xs) {ok = IsNonEmpty} = x :: cycle' xs
  where cycle' : List a -> Stream a
        cycle' []        = x :: cycle' xs
        cycle' (y :: ys) = y :: cycle' ys

Applicative Stream where
  pure = repeat
  (<*>) = zipWith apply

Monad Stream where
  s >>= f = diag (map f s)


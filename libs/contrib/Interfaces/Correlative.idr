module Interfaces.Correlative

import Data.Vect

%access public export
%default total

infixl 3 </>

||| A Correlative functor is a functor where, given `(xs, ys : Correlative f)`,
||| certain elements from xs and ys can be paired with one another due to some
||| intrinsic property of `f`. Elements that cannot be paired are discarded.
interface Functor f => Correlative (f : Type -> Type) where
  (</>) : f (a -> b) -> f a -> f b

infixl 3 </
(</) : Correlative f => f a -> f b -> f a
x </ y = map const x </> y

infixl 3 />
(/>) : Correlative f => f a -> f b -> f b
x /> y = map (const id) x </> y

||| Combine two containers elementwise using some function.
zipWith : Correlative f => (a -> b -> c) -> f a -> f b -> f c
zipWith f xs ys = (map f xs) </> ys

||| Combine three containers elementwise using some function.
zipWith3 : Correlative f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
zipWith3 f xs ys zs = (map f xs) </> ys </> zs

||| Combine two containers elementwise into a container of pairs.
zip : Correlative f => f a -> f b -> f (a, b)
zip = zipWith (\x, y => (x, y))

||| Combine three containers elementwise into a container of tuples.
zip3 : Correlative f => f a -> f b -> f c -> f (a, b, c)
zip3 = zipWith3 (\x, y, z => (x, y, z))

||| Convert a container of pairs into a pair of containers.
unzip : Functor t => t (a, b) -> (t a, t b)
unzip xs = (map fst xs, map snd xs)

||| Convert a container of tuples into a tuple of containers.
unzip3 : Functor t => t (a, b, c) -> (t a, t b, t c)
unzip3 xs = (map fst xs, unzip (map snd xs))

Correlative Maybe where
  (</>) = (<*>)

Correlative (Either a) where
  (</>) = (<*>)

Correlative List where
  (</>) [] _ = []
  (</>) _ [] = []
  (</>) (f :: fs) (x :: xs) = f x :: (fs </> xs)

Correlative Stream where
  (</>) = (<*>)

Correlative (Vect n) where
  (</>) = (<*>)

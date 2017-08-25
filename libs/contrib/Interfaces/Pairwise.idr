module Interfaces.Pairwise

import Data.Vect

%access public export
%default total

infixl 2 </>

||| A Pairwise functor is similar to an Applicative functor which
||| applies operations element-wise.
interface Functor f => Pairwise (f : Type -> Type) where
  (</>) : f (a -> b) -> f a -> f b

||| Combine two containers elementwise using some function.
zipWith : Pairwise f => (a -> b -> c) -> f a -> f b -> f c
zipWith f xs ys = (map f xs) </> ys

||| Combine three containers elementwise using some function.
zipWith3 : Pairwise f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
zipWith3 f xs ys zs = (map f xs) </> ys </> zs

||| Combine two containers elementwise into a container of pairs.
zip : Pairwise f => f a -> f b -> f (a, b)
zip = zipWith (\x, y => (x, y))

||| Combine three containers elementwise into a container of tuples.
zip3 : Pairwise f => f a -> f b -> f c -> f (a, b, c)
zip3 = zipWith3 (\x, y, z => (x, y, z))

||| Convert a container of pairs into a pair of containers.
unzip : Functor t => t (a, b) -> (t a, t b)
unzip xs = (map fst xs, map snd xs)

||| Convert a container of tuples into a tuple of containers.
unzip3 : Functor t => t (a, b, c) -> (t a, t b, t c)
unzip3 xs = (map fst xs, unzip (map snd xs))

Pairwise Maybe where
  (</>) = (<*>)

Pairwise (Either a) where
  (</>) = (<*>)

Pairwise List where
  (</>) [] _ = []
  (</>) _ [] = []
  (</>) (f :: fs) (x :: xs) = f x :: (fs </> xs)

Pairwise Stream where
  (</>) = (<*>)

Pairwise (Vect n) where
  (</>) = (<*>)

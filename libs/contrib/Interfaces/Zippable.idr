module Interfaces.Zippable

import Data.Vect

%access public export
%default total

||| The Zippable interface describes the operation of combining
||| two parameterized container elementwise using a provided function
||| into a new container with the function's return values.
interface Zippable (t : Type -> Type) where
  ||| Combine two containers elementwise using some function.
  ||| If the container type is Sized, the following should hold:
  |||     size (zipWith f xs ys) = minimum (size xs) (size ys)
  zipWith : (f : a -> b -> c) -> t a -> t b -> t c

||| Combine two container of pairs from two containers.
zip : Zippable t => t a -> t b -> t (a, b)
zip = zipWith (\x, y => (x, y))

||| Combine three containers by applying a function elementwise.
zipWith3 : Zippable t => (f : a -> b -> c -> d) -> t a -> t b -> t c -> t d
zipWith3 f xs ys zs = zipWith (\x, (y, z) => f x y z) xs (zip ys zs)

||| Combine three containers into a container of tuples.
zip3 : Zippable t => t a -> t b -> t c -> t (a, b, c)
zip3 = zipWith3 (\x, y, z => (x, y, z))

||| Convert a container of pairs until a pair of containers.
unzip : Functor t => t (a, b) -> (t a, t b)
unzip xs = (map fst xs, map snd xs)

||| Convert a container of tuples into a tuple of containers.
unzip3 : Functor t => t (a, b, c) -> (t a, t b, t c)
unzip3 xs = (map fst xs, unzip (map snd xs))

Zippable Maybe where
  zipWith = liftA2

Zippable (Either a) where
  zipWith = liftA2

Zippable List where
  zipWith = Prelude.List.zipWith

Zippable Stream where
  zipWith = Prelude.Stream.zipWith  

Zippable (Vect n) where
  zipWith = Data.Vect.zipWith

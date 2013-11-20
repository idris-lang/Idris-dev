module Prelude.Stream

import Prelude.Functor
import Prelude.Vect

%access public
%default total

codata Stream : Type -> Type where
  (::) : a -> Stream a -> Stream a

instance Functor Stream where
    map f (x::xs) = f x :: map f xs

head : Stream a -> a
head (x::xs) = x

tail : Stream a -> Stream a
tail (x::xs) = xs

take : (n : Nat) -> Stream a -> Vect n a
take Z _ = []
take (S n) (x :: xs) = x :: (take n xs)

%assert_total
drop : Nat -> Stream a -> Stream a
drop Z xs = xs
drop (S k) (x::xs) = drop k xs

repeat : a -> Stream a
repeat x = x :: repeat x

iterate : (a -> a) -> a -> Stream a
iterate f x = x :: iterate f (f x)

index : Nat -> Stream a -> a
index Z (x::xs) = x
index (S k) (x::xs) = index k xs

zipWith : (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

zip : Stream a -> Stream b -> Stream (a, b)
zip = zipWith (\x,y => (x,y))

unzip : Stream (a, b) -> (Stream a, Stream b)
unzip xs = (map fst xs, map snd xs)

diag : Stream (Stream a) -> Stream a
diag ((x::xs)::xss) = x :: diag (map tail xss)



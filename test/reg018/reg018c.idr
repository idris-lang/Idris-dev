module CodataTest
import Data.Vect

%default total

codata InfStream a = (::) a (InfStream a)
--
-- natStream : InfStream Nat
-- natStream = natFromStream 0 where
--   natFromStream : Nat -> InfStream Nat
--   natFromStream n = (::) n (natFromStream (S n))

take : (n: Nat) -> InfStream a -> Vect n a
take Z _ = []
take (S n) (x :: xs) = x :: CodataTest.take n xs

hdtl : InfStream a -> (a, InfStream a)
hdtl (x :: xs) = (x, xs)

inf : InfStream a -> InfStream a
inf (x :: xs) with (hdtl xs)
  | (hd, tl) = inf xs

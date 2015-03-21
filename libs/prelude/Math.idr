module Math

import Builtins
import Prelude.Basics
import Prelude.Classes
import Prelude.Nat
import Prelude.Either
import Prelude.Functor
import Decidable.Equality

%access public
%default total

--------------------------------------------------------------------------------
-- GCD and LCM
--------------------------------------------------------------------------------
gcd : Nat -> Nat -> Nat
gcd a b = case decEq b Z of
  Yes  => a
  No p => assert_total (gcd b (modNat a b p))

lcm : Nat -> Nat -> Nat
lcm x y =
  let g: Nat = (gcd x y) in
  case decEq g Z of
    Yes _ => Z
    No p  => divNat (x * y) g p

-- div and mod
div: (Integral a, DecEq a) => a -> (y: a) -> Either (y = zero) a
div x y = case decEq y zero of
  Yes p => Left p
  No p  => Right (divNZ x y p)

mod: (Integral a, DecEq a) => a -> (y: a) -> Either (y = zero) a
mod x y = case decEq y zero of
  Yes p => Left p
  No p  => Right (modNZ x y p)

private
twoNotZ: (S (S Z) = Z) -> Void
twoNotZ Refl impossible

log2 : (n: Nat) -> Either (n = Z) Nat
log2 Z     = Left Refl
log2 n     = case log2 (assert_smaller n (divNat n 2 twoNotZ)) of
  Left _  => Right Z
  Right x => Right (S x)


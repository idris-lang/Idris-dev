module Algebra.Nat

import Builtins

import Algebra.AbstractAlgebra

%access public
%default total

--------------------------------------------------------------------------------
-- Type class instances
--------------------------------------------------------------------------------

||| A wrapper for Nat that specifies the semigroup and monad instances that use (+)
record Multiplicative : Type where
  getMultiplicative : Nat -> Multiplicative

||| A wrapper for Nat that specifies the semigroup and monad instances that use (*)
record Additive : Type where
  getAdditive : Nat -> Additive

instance Semigroup Multiplicative where
  (<+>) left right = getMultiplicative $ left' * right'
    where
      left'  : Nat
      left'  =
       case left of
          getMultiplicative m => m

      right' : Nat
      right' =
        case right of
          getMultiplicative m => m

instance Semigroup Additive where
  left <+> right = getAdditive $ left' + right'
    where
      left'  : Nat
      left'  =
        case left of
          getAdditive m => m

      right' : Nat
      right' =
        case right of
          getAdditive m => m

instance Monoid Multiplicative where
  neutral = getMultiplicative $ S Z

instance Monoid Additive where
  neutral = getAdditive Z

instance MeetSemilattice Nat where
  meet = minimum

instance JoinSemilattice Nat where
  join = maximum

instance Lattice Nat where { }

instance BoundedJoinSemilattice Nat where
  bottom = Z

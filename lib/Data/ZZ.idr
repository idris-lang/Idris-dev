module Data.ZZ

import Decidable.Equality
import Data.Sign

%default total
%access public


-- | An integer is either a positive nat or the negated successor of a nat.
-- Zero is chosen to be positive.
data ZZ = Pos Nat | NegS Nat

instance Signed ZZ where
  sign (Pos _) = Plus
  sign (NegS _) = Minus

absZ : ZZ -> Nat
absZ (Pos n) = n
absZ (NegS n) = S n

instance Show ZZ where
  show (Pos n) = show n
  show (NegS n) = "-" ++ show (S n)

negZ : ZZ -> ZZ
negZ (Pos Z) = Pos Z
negZ (Pos (S n)) = NegS n
negZ (NegS n) = Pos (S n)

negNat : Nat -> ZZ
negNat Z = Pos Z
negNat (S n) = NegS n

minusNatZ : Nat -> Nat -> ZZ
minusNatZ n Z = Pos n
minusNatZ Z (S m) = NegS m
minusNatZ (S n) (S m) = minusNatZ n m

plusZ : ZZ -> ZZ -> ZZ
plusZ (Pos n) (Pos m) = Pos (n + m)
plusZ (NegS n) (NegS m) = NegS (S (n + m))
plusZ (Pos n) (NegS m) = minusNatZ n (S m)
plusZ (NegS n) (Pos m) = minusNatZ m (S n)

subZ : ZZ -> ZZ -> ZZ
subZ n m = plusZ n (negZ m)

instance Eq ZZ where
  (Pos n) == (Pos m) = n == m
  (NegS n) == (NegS m) = n == m
  _ == _ = False


instance Ord ZZ where
  compare (Pos n) (Pos m) = compare n m
  compare (NegS n) (NegS m) = compare m n
  compare (Pos _) (NegS _) = GT
  compare (NegS _) (Pos _) = LT


multZ : ZZ -> ZZ -> ZZ
multZ (Pos n) (Pos m) = Pos $ n * m
multZ (NegS n) (NegS m) = Pos $ (S n) * (S m)
multZ (NegS n) (Pos m) = negNat $ (S n) * m
multZ (Pos n) (NegS m) = negNat $ n * (S m)

fromInt : Integer -> ZZ
fromInt n = if n < 0
            then NegS $ fromInteger {a=Nat} (-n - 1)
            else Pos $ fromInteger {a=Nat} n

instance Cast Nat ZZ where
  cast n = Pos n

instance Num ZZ where
  (+) = plusZ
  (-) = subZ
  (*) = multZ
  abs = cast . absZ
  fromInteger = fromInt

instance Cast ZZ Integer where
  cast (Pos n) = cast n
  cast (NegS n) = (-1) * (cast n + 1)

instance Cast Integer ZZ where
  cast = fromInteger


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

natPlusZPlus : (n : Nat) -> (m : Nat) -> (x : Nat)
             -> n + m = x -> (Pos n) + (Pos m) = Pos x
natPlusZPlus n m x h = cong h

natMultZMult : (n : Nat) -> (m : Nat) -> (x : Nat)
             -> n * m = x -> (Pos n) * (Pos m) = Pos x
natMultZMult n m x h = cong h

doubleNegElim : (z : ZZ) -> negZ (negZ z) = z
doubleNegElim (Pos Z) = refl
doubleNegElim (Pos (S n)) = refl
doubleNegElim (NegS Z) = refl
doubleNegElim (NegS (S n)) = refl

-- Injectivity
posInjective : Pos n = Pos m -> n = m
posInjective refl = refl

negSInjective : NegS n = NegS m -> n = m
negSInjective refl = refl

posNotNeg : Pos n = NegS m -> _|_
posNotNeg refl impossible

-- Decidable equality
instance DecEq ZZ where
  decEq (Pos n) (NegS m) = No posNotNeg
  decEq (NegS n) (Pos m) = No $ negEqSym posNotNeg
  decEq (Pos n) (Pos m) with (decEq n m)
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ posInjective h
  decEq (NegS n) (NegS m) with (decEq n m)
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ negSInjective h

-- Plus
plusZeroLeftNeutralZ : (right : ZZ) -> 0 + right = right
plusZeroLeftNeutralZ (Pos n) = refl
plusZeroLeftNeutralZ (NegS n) = refl

plusZeroRightNeutralZ : (left : ZZ) -> left + 0 = left
plusZeroRightNeutralZ (Pos n) = cong $ plusZeroRightNeutral n
plusZeroRightNeutralZ (NegS n) = refl

plusCommutativeZ : (left : ZZ) -> (right : ZZ) -> (left + right = right + left)
plusCommutativeZ (Pos n) (Pos m) = cong $ plusCommutative n m
plusCommutativeZ (Pos n) (NegS m) = refl
plusCommutativeZ (NegS n) (Pos m) = refl
plusCommutativeZ (NegS n) (NegS m) = cong {f=NegS} $ cong {f=S} $ plusCommutative n m


module Data.ZZ

import Decidable.Equality
import Data.Sign

%default total
%access public export

||| An integer is either a positive `Nat` or the negated successor of a `Nat`.
|||
||| For example, 3 is `Pos 3` and -2 is `NegS 1`. Zero is arbitrarily chosen
||| to be positive.
|||
data ZZ = Pos Nat | NegS Nat

implementation Signed ZZ where
  sign (Pos Z) = Zero
  sign (Pos _) = Plus
  sign (NegS _) = Minus

||| Take the absolute value of a `ZZ`
absZ : ZZ -> Nat
absZ (Pos n) = n
absZ (NegS n) = S n

implementation Show ZZ where
  show (Pos n) = show n
  show (NegS n) = "-" ++ show (S n)

negNat : Nat -> ZZ
negNat Z = Pos Z
negNat (S n) = NegS n


||| Construct a `ZZ` as the difference of two `Nat`s
minusNatZ : Nat -> Nat -> ZZ
minusNatZ n Z = Pos n
minusNatZ Z (S m) = NegS m
minusNatZ (S n) (S m) = minusNatZ n m

||| Add two `ZZ`s. Consider using `(+) {a=ZZ}`.
plusZ : ZZ -> ZZ -> ZZ
plusZ (Pos n) (Pos m) = Pos (n + m)
plusZ (NegS n) (NegS m) = NegS (S (n + m))
plusZ (Pos n) (NegS m) = minusNatZ n (S m)
plusZ (NegS n) (Pos m) = minusNatZ m (S n)

implementation Eq ZZ where
  (Pos n) == (Pos m) = n == m
  (NegS n) == (NegS m) = n == m
  _ == _ = False

implementation Ord ZZ where
  compare (Pos n) (Pos m) = compare n m
  compare (NegS n) (NegS m) = compare m n
  compare (Pos _) (NegS _) = GT
  compare (NegS _) (Pos _) = LT

||| Multiply two `ZZ`s. Consider using `(*) {a=ZZ}`.
multZ : ZZ -> ZZ -> ZZ
multZ (Pos n) (Pos m) = Pos $ n * m
multZ (NegS n) (NegS m) = Pos $ (S n) * (S m)
multZ (NegS n) (Pos m) = negNat $ (S n) * m
multZ (Pos n) (NegS m) = negNat $ n * (S m)

||| Convert an `Integer` to an inductive representation.
fromInt : Integer -> ZZ
fromInt n = if n < 0
            then NegS $ fromInteger ((-n) - 1)
            else Pos $ fromInteger n

implementation Cast Nat ZZ where
  cast n = Pos n

implementation Num ZZ where
  (+) = plusZ
  (*) = multZ
  fromInteger = fromInt

mutual
  implementation Neg ZZ where
    negate (Pos Z)     = Pos Z
    negate (Pos (S n)) = NegS n
    negate (NegS n)    = Pos (S n)

    (-) = subZ
    abs = cast . absZ

  ||| Subtract two `ZZ`s. Consider using `(-) {a=ZZ}`.
  subZ : ZZ -> ZZ -> ZZ
  subZ n m = plusZ n (negate m)

implementation Cast ZZ Integer where
  cast (Pos n) = cast n
  cast (NegS n) = (-1) * (cast n + 1)

implementation Cast Integer ZZ where
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

doubleNegElim : (z : ZZ) -> negate (negate z) = z
doubleNegElim (Pos Z) = Refl
doubleNegElim (Pos (S n)) = Refl
doubleNegElim (NegS Z) = Refl
doubleNegElim (NegS (S n)) = Refl

-- Injectivity
posInjective : Pos n = Pos m -> n = m
posInjective Refl = Refl

negSInjective : NegS n = NegS m -> n = m
negSInjective Refl = Refl

posNotNeg : Pos n = NegS m -> Void
posNotNeg Refl impossible

-- Decidable equality
implementation DecEq ZZ where
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
plusZeroLeftNeutralZ (Pos n) = Refl
plusZeroLeftNeutralZ (NegS n) = Refl

plusZeroRightNeutralZ : (left : ZZ) -> left + 0 = left
plusZeroRightNeutralZ (Pos n) = cong $ plusZeroRightNeutral n
plusZeroRightNeutralZ (NegS n) = Refl

plusCommutativeZ : (left : ZZ) -> (right : ZZ) -> (left + right = right + left)
plusCommutativeZ (Pos n) (Pos m) = cong $ plusCommutative n m
plusCommutativeZ (Pos n) (NegS m) = Refl
plusCommutativeZ (NegS n) (Pos m) = Refl
plusCommutativeZ (NegS n) (NegS m) = cong {f=NegS} $ cong {f=S} $ plusCommutative n m

minusNatZAntiCommutative : (j, k : Nat) -> negate (minusNatZ j k) = minusNatZ k j
minusNatZAntiCommutative Z Z = Refl
minusNatZAntiCommutative Z (S k) = Refl
minusNatZAntiCommutative (S j) Z = Refl
minusNatZAntiCommutative (S j) (S k) = minusNatZAntiCommutative j k

negateDistributesPlus : (a, b : ZZ) -> negate (a + b) = (negate a) + (negate b)
negateDistributesPlus (Pos Z) b = rewrite plusZeroLeftNeutralZ b in
                                  rewrite plusZeroLeftNeutralZ (negate b) in Refl
negateDistributesPlus (Pos (S k)) (Pos Z) = rewrite plusZeroRightNeutral k in Refl
negateDistributesPlus (Pos (S k)) (Pos (S j)) = rewrite plusCommutative k (S j) in
                                                rewrite plusCommutative j k in Refl
negateDistributesPlus (Pos (S k)) (NegS j) = minusNatZAntiCommutative k j
negateDistributesPlus (NegS k) (Pos Z) = rewrite plusZeroRightNeutral k in Refl
negateDistributesPlus (NegS k) (Pos (S j)) = minusNatZAntiCommutative j k
negateDistributesPlus (NegS k) (NegS j) = rewrite plusCommutative k (S j) in
                                          rewrite plusCommutative k j in Refl

lemmaMinusSucc : (k, j, i : Nat) -> plusZ (minusNatZ k (S j)) (Pos i) = plusZ (minusNatZ k (S (S j))) (Pos (S i))
lemmaMinusSucc Z j i = Refl
lemmaMinusSucc (S Z) Z i = Refl
lemmaMinusSucc (S (S k)) Z i = rewrite plusCommutative k (S i) in
                               rewrite plusCommutative i k in Refl
lemmaMinusSucc (S k) (S j) i = lemmaMinusSucc k j i

lemmaAssocNegation : (k : Nat) -> (c, r : ZZ) -> (Pos (S k)) + (c + r) = ((Pos (S k)) + c) + r -> (NegS k) + ((negate c) + (negate r)) = ((NegS k) + (negate c)) + (negate r)
lemmaAssocNegation k c r prf = rewrite sym $ negateDistributesPlus c r in
                               rewrite sym $ negateDistributesPlus (Pos (S k)) (plusZ c r) in
                               rewrite sym $ negateDistributesPlus (Pos (S k)) c in
                               rewrite sym $ negateDistributesPlus (plusZ (Pos (S k)) c) r in
                               cong $ prf

lemmaAssocPos : (k : Nat) -> (c, r : ZZ) -> (Pos k) + (c + r) = ((Pos k) + c) + r
lemmaAssocPos k (Pos j) (Pos i) = cong $ plusAssociative k j i
lemmaAssocPos k (Pos Z) (NegS i) = rewrite plusZeroRightNeutral k in Refl
lemmaAssocPos k (Pos (S j)) (NegS Z) = rewrite plusCommutative k (S j) in
                                       rewrite plusCommutative j k in Refl
lemmaAssocPos k (Pos (S j)) (NegS (S i)) = let ind = lemmaAssocPos k (assert_smaller (Pos (S j)) (Pos j)) (assert_smaller (NegS (S i)) (NegS i)) in
                                           rewrite ind in
                                           rewrite plusCommutative k (S j) in
                                           rewrite plusCommutative j k in Refl
lemmaAssocPos k (NegS j) (Pos Z) = rewrite plusZeroRightNeutralZ (minusNatZ k (S j)) in Refl
lemmaAssocPos Z (NegS Z) (Pos (S i)) = Refl
lemmaAssocPos (S k) (NegS Z) (Pos (S i)) = rewrite plusCommutative k (S i) in
                                           rewrite plusCommutative k i in Refl
lemmaAssocPos k (NegS (S j)) (Pos (S i)) = let ind = lemmaAssocPos k (assert_smaller (NegS (S j)) (NegS j)) (assert_smaller (Pos (S i)) (Pos i)) in
                                           rewrite ind in
                                           rewrite lemmaMinusSucc k j i in Refl
lemmaAssocPos Z (NegS j) (NegS i) = Refl
lemmaAssocPos (S k) (NegS Z) (NegS i) = Refl
lemmaAssocPos (S k) (NegS (S j)) (NegS i) = let ind = lemmaAssocPos (assert_smaller (S k) k) (assert_smaller (NegS (S j)) (NegS j)) (NegS i) in
                                            rewrite ind in Refl

plusAssociativeZ : (l, c, r : ZZ) -> l + (c + r) = (l + c) + r
plusAssociativeZ (Pos k) c r = lemmaAssocPos k c r
plusAssociativeZ (NegS k) c r = rewrite sym $ doubleNegElim c in
                                rewrite sym $ doubleNegElim r in
                                lemmaAssocNegation k (negate c) (negate r) (lemmaAssocPos (S k) (negate c) (negate r))

lemmaMinusSymmZero : (k : Nat) -> minusNatZ k k = Pos 0
lemmaMinusSymmZero Z = Refl
lemmaMinusSymmZero (S k) = let ind = lemmaMinusSymmZero k in
                           rewrite ind in Refl

plusNegateInverseLZ : (a : ZZ) -> a + negate a = Pos Z
plusNegateInverseLZ (Pos Z) = Refl
plusNegateInverseLZ (Pos (S k)) = rewrite lemmaMinusSymmZero k in Refl
plusNegateInverseLZ (NegS k) = rewrite lemmaMinusSymmZero k in Refl

plusNegateInverseRZ : (a : ZZ) -> negate a + a = Pos Z
plusNegateInverseRZ (Pos Z) = Refl
plusNegateInverseRZ (Pos (S k)) = rewrite lemmaMinusSymmZero k in Refl
plusNegateInverseRZ (NegS k) = rewrite lemmaMinusSymmZero k in Refl

-- Mult
multZeroLeftZeroZ : (right : ZZ) -> (Pos Z) * right = (Pos Z)
multZeroLeftZeroZ (Pos k) = Refl
multZeroLeftZeroZ (NegS k) = Refl

multZeroRightZeroZ : (left : ZZ) -> left * (Pos Z) = (Pos Z)
multZeroRightZeroZ (Pos k) = rewrite multZeroRightZero k in Refl
multZeroRightZeroZ (NegS k) = rewrite multZeroRightZero k in Refl

multOneLeftNeutralZ : (right : ZZ) -> 1 * right = right
multOneLeftNeutralZ (Pos k) = rewrite plusZeroRightNeutral k in Refl
multOneLeftNeutralZ (NegS k) = rewrite plusZeroRightNeutral k in Refl

multOneRightNeutralZ : (left : ZZ) -> left * 1 = left
multOneRightNeutralZ (Pos Z) = Refl
multOneRightNeutralZ (Pos (S k)) = cong $ multOneRightNeutral (S k)
multOneRightNeutralZ (NegS k) = cong $ multOneRightNeutral k

multCommutativeZ : (left : ZZ) -> (right : ZZ) -> (left * right = right * left)
multCommutativeZ (Pos k) (Pos j) = cong $ multCommutative k j
multCommutativeZ (Pos k) (NegS j) = rewrite multCommutative j k in
                                    cong $ multRightSuccPlus k j
multCommutativeZ (NegS k) (Pos j) = rewrite multCommutative j (S k) in Refl
multCommutativeZ (NegS k) (NegS j) = cong $ multCommutative (S k) (S j)

lemmaPosMultNegNat : (k, j : Nat) -> multZ (Pos k) (negNat j) = negNat (mult k j)
lemmaPosMultNegNat k Z = rewrite multZeroRightZero k in Refl
lemmaPosMultNegNat k (S j) = Refl

lemmaNegMultNegNat : (k, j : Nat) -> multZ (NegS k) (negNat j) = multZ (Pos (S k)) (Pos j)
lemmaNegMultNegNat k Z = rewrite multZeroRightZero k in Refl
lemmaNegMultNegNat k (S j) = Refl

lemmaNegatePosNegNat : (k : Nat) -> negate (Pos k) = negNat k
lemmaNegatePosNegNat Z = Refl
lemmaNegatePosNegNat (S k) = Refl

multNegLeftZ : (k : Nat) -> (j : ZZ) -> (NegS k) * j = negate (Pos (S k) * j)
multNegLeftZ k (Pos j) = rewrite lemmaNegatePosNegNat ((S k) * j) in Refl
multNegLeftZ k (NegS j) = Refl

multNegateLeftZ : (k, j : ZZ) -> (negate k) * j = negate (k * j)
multNegateLeftZ (Pos Z) j = rewrite multZeroLeftZeroZ j in Refl
multNegateLeftZ (Pos (S k)) (Pos j) = rewrite lemmaNegatePosNegNat ((S k) * j) in Refl
multNegateLeftZ (Pos (S k)) (NegS j) = Refl
multNegateLeftZ (NegS k) j = rewrite sym $ doubleNegElim (multZ (Pos (S k)) j) in
                             rewrite multNegLeftZ k j in Refl

multAssociativeZPos : (k : Nat) -> (c, r : ZZ) -> (Pos k) * (c * r) = ((Pos k) * c) * r
multAssociativeZPos k (Pos j) (Pos i) = cong $ multAssociative k j i
multAssociativeZPos k (Pos j) (NegS i) = rewrite sym $ multAssociative k j (S i) in lemmaPosMultNegNat k (mult j (S i))
multAssociativeZPos k (NegS j) (Pos i) = rewrite multCommutative j i in
                                         rewrite sym $ multRightSuccPlus i j in
                                         rewrite lemmaPosMultNegNat k (mult i (S j)) in
                                         rewrite multCommutativeZ (negNat (mult k (S j))) (Pos i) in
                                         rewrite lemmaPosMultNegNat i (mult k (S j)) in
                                         rewrite multAssociative k i (S j) in
                                         rewrite multAssociative i k (S j) in
                                         rewrite multCommutative i k in Refl
multAssociativeZPos k (NegS j) (NegS i) = rewrite multCommutativeZ (negNat (mult k (S j))) (NegS i) in
                                          rewrite lemmaNegMultNegNat i (mult k (S j)) in
                                          rewrite multAssociative k (S j) (S i) in
                                          rewrite multCommutative (mult k (S j)) (S i) in Refl

multAssociativeZ : (l, c, r : ZZ) -> l * (c * r) = (l * c) * r
multAssociativeZ (Pos k) c r = multAssociativeZPos k c r
multAssociativeZ (NegS k) c r = rewrite multNegLeftZ k (c * r) in
                                rewrite multNegLeftZ k c in
                                rewrite multNegateLeftZ (multZ (Pos (S k)) c) r in
                                cong $ multAssociativeZPos (S k) c r

lemmaPlusPosNegCancel : (k, j, i : Nat) -> plusZ (Pos (plus k j)) (negNat (plus k i)) = plusZ (Pos j) (negNat i)
lemmaPlusPosNegCancel Z j i = Refl
lemmaPlusPosNegCancel (S Z) j Z = rewrite plusZeroRightNeutral j in Refl
lemmaPlusPosNegCancel (S Z) j (S i) = Refl
lemmaPlusPosNegCancel (S (S k)) j i = lemmaPlusPosNegCancel (S k) j i

lemmaPlusPosNegZero : (k : Nat) -> plusZ (Pos k) (negNat k) = Pos Z
lemmaPlusPosNegZero Z = Refl
lemmaPlusPosNegZero (S k) = rewrite lemmaMinusSymmZero k in Refl

negNatDistributesPlus : (j, k : Nat) -> plusZ (negNat j) (negNat k) = negNat (plus j k)
negNatDistributesPlus Z k = rewrite plusZeroLeftNeutralZ (negNat k) in Refl
negNatDistributesPlus (S j) Z = rewrite plusZeroRightNeutral j in Refl
negNatDistributesPlus (S j) (S k) = rewrite plusSuccRightSucc j k in Refl

-- Distributivity

multDistributesOverPlusRightPosPosZ : (l, c : Nat) -> (r : ZZ) -> (Pos l) * ((Pos c) + r) = ((Pos l) * (Pos c)) + ((Pos l) * r)
multDistributesOverPlusRightPosPosZ l c (Pos i) = rewrite multDistributesOverPlusRight l c i in Refl
multDistributesOverPlusRightPosPosZ l Z (NegS i) = rewrite multZeroRightZero l in
                                                   rewrite plusZeroLeftNeutralZ (negNat (mult l (S i))) in Refl
multDistributesOverPlusRightPosPosZ l (S c) (NegS Z) = rewrite multOneRightNeutral l in
                                                       rewrite multRightSuccPlus l c in
                                                       rewrite sym $ plusAssociativeZ (Pos l) (Pos (mult l c)) (negNat l) in
                                                       rewrite plusCommutativeZ (Pos (mult l c)) (negNat l) in
                                                       rewrite plusAssociativeZ (Pos l) (negNat l) (Pos (mult l c)) in
                                                       rewrite lemmaPlusPosNegZero l in Refl
multDistributesOverPlusRightPosPosZ l (S c) (NegS (S i)) = let ind = multDistributesOverPlusRightPosPosZ l (assert_smaller (S c) c) (assert_smaller (NegS (S i)) (NegS i)) in
                                                           rewrite ind in
                                                           rewrite multRightSuccPlus l (S i) in
                                                           rewrite multRightSuccPlus l c in
                                                           rewrite lemmaPlusPosNegCancel l (mult l c) (mult l (S i)) in Refl

multDistributesOverPlusRightPosZ : (k : Nat) -> (c, r : ZZ) -> (Pos k) * (c + r) = ((Pos k) * c) + ((Pos k) * r)
multDistributesOverPlusRightPosZ k (Pos j) r = multDistributesOverPlusRightPosPosZ k j r
multDistributesOverPlusRightPosZ k (NegS j) (Pos i) = rewrite plusCommutativeZ ((Pos k) * (NegS j)) ((Pos k) * (Pos i)) in
                                                      rewrite multDistributesOverPlusRightPosPosZ k i (NegS j) in Refl
multDistributesOverPlusRightPosZ k (NegS j) (NegS i) = rewrite negNatDistributesPlus (mult k (S j)) (mult k (S i)) in
                                                       rewrite sym $ multDistributesOverPlusRight k (S j) (S i) in
                                                       rewrite plusSuccRightSucc j i in Refl

multDistributesOverPlusRightZ : (l, c, r : ZZ) -> l * (c + r) = (l * c) + (l * r)
multDistributesOverPlusRightZ (Pos k) c r = multDistributesOverPlusRightPosZ k c r
multDistributesOverPlusRightZ (NegS k) c r = rewrite multNegLeftZ k (plusZ c r) in
                                             rewrite multNegLeftZ k c in
                                             rewrite multNegLeftZ k r in
                                             rewrite sym $ negateDistributesPlus (multZ (Pos (S k)) c) (multZ (Pos (S k)) r) in
                                             rewrite multDistributesOverPlusRightPosZ (S k) c r in Refl

multDistributesOverPlusLeftZ : (l, c, r : ZZ) -> (l + c) * r = (l * r) + (c * r)
multDistributesOverPlusLeftZ l c r = rewrite multCommutativeZ (l + c) r in
                                     rewrite multDistributesOverPlusRightZ r l c in
                                     rewrite multCommutativeZ r l in
                                     rewrite multCommutativeZ r c in Refl

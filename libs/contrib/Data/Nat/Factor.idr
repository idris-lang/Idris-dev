module Data.Nat.Factor

import Data.Fin
import Data.Fin.Extra
import Data.Nat

%default total
%access export


data FactorsOf : Nat -> (Nat, Nat) -> Type where
    FactorPair : (n, p, q : Nat) -> LTE 1 n -> p * q = n -> FactorsOf n (p, q)

data NotFactorsOf : Nat -> (Nat, Nat) -> Type where
    NotFactorPair : (n, p, q, r : Nat) -> LTE 1 n -> p * q + S r = n -> NotFactorsOf n (p, q)

data Factor : Nat -> Nat -> Type where
    CoFactorExists : {n, f : Nat} -> (q : Nat) -> FactorsOf n (f, q) -> Factor n f

data NotFactor : Nat -> Nat -> Type where
    ProperRemExists : (n, p, q : Nat) ->
        (r : Fin (pred p)) ->
        LTE 1 n ->
        p * q + S (finToNat r) = n ->
        NotFactor n p

data DecFactor : Nat -> Nat -> Type where
    ItIsFactor : Factor n f -> DecFactor n f
    ItIsNotFactor : NotFactor n f -> DecFactor n f

Uninhabited (FactorsOf 0 p) where
    uninhabited (FactorPair n _ _ poistN _) impossible

Uninhabited (FactorsOf n (0, a)) where
    uninhabited (FactorPair n Z a posN prf) =
            succNotLTEzero $ replace {P = LTE 1} (sym prf) posN

Uninhabited (FactorsOf n (a, 0)) where
    uninhabited (FactorPair n a Z posN prf) =
        let zeroIsN = replace {P = \x => x = n} (multZeroRightZero a) prf in
        succNotLTEzero $ replace {P = LTE 1} (sym zeroIsN) posN


Uninhabited (Factor Z f) where
    uninhabited (CoFactorExists q prf) = uninhabited prf

factPairNotFactPairAbsurd : FactorsOf n (p, q) -> NotFactorsOf n (p, q) -> Void
factPairNotFactPairAbsurd (FactorPair n p q _ prf) (NotFactorPair _ _ _ r _ contra) =
        plusSuccIsNotIdentity $ replace {P = \a => a + S r = n} prf contra


factorNotFactorAbsurd : Factor n p -> NotFactor n p -> Void
factorNotFactorAbsurd (CoFactorExists q (FactorPair n p q positN prf)) (ProperRemExists n p q' r _ contra) =
        thisIsAbsurd q q' prf $ replace {P = \x => (p * q') + S (finToNat r) = x} (sym prf) contra
    where
    thisIsAbsurd : (q, q' : Nat) -> p * q = n -> (p * q') + S (finToNat r) = p * q -> Void
    thisIsAbsurd q q' nIsPQ a with (cmp q q')
        thisIsAbsurd q (q + S d) nIsPQ a  | CmpLT d =
            plusSuccIsNotIdentity .
            replace {P = \x => (p * q) + x = p * q} (sym $ plusSuccRightSucc (p * S d) (finToNat r)) .
            replace {P = \x => x = p * q} (sym $ plusAssociative (p * q) (p * S d) (S $ finToNat r)) $
            replace {P = \x => x + S (finToNat r) = p * q} (multDistributesOverPlusRight p q (S d)) a
        thisIsAbsurd q q nIsPQ a          | CmpEQ = plusSuccIsNotIdentity a
        thisIsAbsurd (q + S d) q nIsPQ a  | CmpGT d =
            let defSr =
                    replace {P = \x => S (finToNat r) = x} (multRightSuccPlus p d) .
                    subtractEqLeft $
                    replace {P = \x => (p * q) + S (finToNat r) = x} (multDistributesOverPlusRight p q (S d)) a
                (_ ** nIsSucc) = lteToSucc positN
                pGtZ = nonZeroLeftFactor $ replace {P = \x => p * (q + S d) = x} nIsSucc nIsPQ
            in
            succNotLTEzero . subtractLteLeft .
            replace {P = \x => LTE (p + S (p * d)) x} (sym $ plusZeroRightNeutral p) .
            replace {P = \x => LTE x p} (plusSuccRightSucc p (p * d)) .
            replace {P = \x => LTE (S x) p} defSr .
            replace {P = LTE (S (S (finToNat r)))} (succPred p {ok = pGtZ}) $
            LTESucc $ elemSmallerThanBound r


swapFactors : FactorsOf n (a, b) -> FactorsOf n (b, a)
swapFactors (FactorPair n a b positN prf) =
        FactorPair n b a positN (rewrite multCommutative b a in prf)


oneAndSeflAreFactors : (n : Nat) -> {auto ok : LTE 1 n} -> FactorsOf n (n, 1)
oneAndSeflAreFactors n {ok} = FactorPair n n 1 ok (multOneRightNeutral n)

oneIsFactor : (n : Nat) -> {auto ok : LTE 1 n} -> Factor n 1
oneIsFactor (S k) {ok} =
        CoFactorExists (S k) (swapFactors $ oneAndSeflAreFactors (S k))

selfFactor : (n : Nat) -> {auto ok : LTE 1 n} -> Factor n n
selfFactor (S k) {ok} = CoFactorExists 1 (oneAndSeflAreFactors (S k))

factorLteNumber : Factor n f -> LTE f n
factorLteNumber (CoFactorExists Z (FactorPair n a Z positN prf)) =
        let nIsZero = replace {P = \x => n = x} (multZeroRightZero a) $ sym prf
            oneLteZero = replace {P = LTE 1} nIsZero positN
        in
        absurd $ succNotLTEzero oneLteZero
factorLteNumber (CoFactorExists (S b) (FactorPair n a (S b) positN prf)) =
        leftFactorLteProduct prf

plusDivisorAlsoFactor : Factor n f -> Factor (n + f) f
plusDivisorAlsoFactor (CoFactorExists q (FactorPair n f q positN prf)) =
        CoFactorExists (S q) $
            FactorPair (n + f) f (S q) (lteTransitive positN $ lteAddRight n) $
                rewrite plusCommutative n f in
                rewrite multRightSuccPlus f q in
                cong {f = plus f} prf

plusDivisorNeitherFactor : NotFactor n f -> NotFactor (n + f) f
plusDivisorNeitherFactor (ProperRemExists n p q r positN remPrf) =
        ProperRemExists (n + p) p (S q) r (lteTransitive positN $ lteAddRight n) (
                rewrite multRightSuccPlus p q in
                rewrite sym $ plusAssociative p (p * q) (S $ finToNat r) in
                rewrite plusCommutative p ((p * q) + S (finToNat r)) in
                rewrite remPrf in
                Refl
            )

decFactor : (n, d : Nat) -> {auto nok : LTE 1 n} -> {auto dok : LTE 1 d} -> DecFactor n d
decFactor n (S d) {nok} {dok} with (Data.Fin.Extra.divMod n (S d))
        | (Fraction n (S d) q r prf) = case r of
                FZ =>
                    let ok =
                            replace {P = \x => x = n} (plusZeroRightNeutral (q + (d * q))) $
                            replace {P = \x => x + 0 = n} (multCommutative q (S d)) prf
                    in
                    ItIsFactor $ CoFactorExists q (FactorPair n (S d) q nok ok)

                (FS pr) =>
                    ItIsNotFactor $ ProperRemExists n (S d) q pr nok (
                            rewrite multCommutative d q in
                            rewrite sym $ multRightSuccPlus q d in
                            prf
                        )

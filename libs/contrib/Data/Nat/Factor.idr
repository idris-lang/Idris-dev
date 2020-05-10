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
    CofactorExists : {n, p : Nat} -> (q : Nat) -> LTE 1 n -> p * q = n -> Factor n p

data NotFactor : Nat -> Nat -> Type where
    ProperRemExists : {n, p : Nat} -> (q : Nat) ->
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


Uninhabited (Factor Z p) where
    uninhabited (CofactorExists {n = Z} _ ok _) = uninhabited ok

cofactor : Factor n p -> (q : Nat ** q * p = n)
cofactor (CofactorExists {n} {p} q ok prf) =
        (q ** rewrite multCommutative q p in prf)

factPairNotFactPairAbsurd : FactorsOf n (p, q) -> NotFactorsOf n (p, q) -> Void
factPairNotFactPairAbsurd (FactorPair n p q _ prf) (NotFactorPair _ _ _ r _ contra) =
        plusSuccIsNotIdentity $ replace {P = \a => a + S r = n} prf contra


factorNotFactorAbsurd : Factor n p -> NotFactor n p -> Void
factorNotFactorAbsurd (CofactorExists {n} {p} q positN prf) (ProperRemExists {n} {p} q' r _ contra) =
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

leftFactor : FactorsOf n (p, q) -> Factor n p
leftFactor (FactorPair n p q ok prf) = CofactorExists q ok prf

rightFactor : FactorsOf n (p, q) -> Factor n q
rightFactor (FactorPair n p q ok prf) = CofactorExists p ok (rewrite multCommutative q p in prf)

oneAndSeflAreFactors : (n : Nat) -> {auto ok : LTE 1 n} -> FactorsOf n (n, 1)
oneAndSeflAreFactors n {ok} = FactorPair n n 1 ok (multOneRightNeutral n)

oneIsFactor : (n : Nat) -> {auto ok : LTE 1 n} -> Factor n 1
oneIsFactor (S k) {ok} =
        CofactorExists (S k) ok (rewrite plusZeroRightNeutral k in Refl)

selfFactor : (n : Nat) -> {auto ok : LTE 1 n} -> Factor n n
selfFactor (S k) {ok} = CofactorExists 1 ok (rewrite multOneRightNeutral k in Refl)

factorLteNumber : Factor n p -> LTE p n
factorLteNumber (CofactorExists {n} {p} Z positN prf) =
        let nIsZero = replace {P = \x => n = x} (multZeroRightZero p) $ sym prf
            oneLteZero = replace {P = LTE 1} nIsZero positN
        in
        absurd $ succNotLTEzero oneLteZero
factorLteNumber (CofactorExists {n} {p} (S k) positN prf) =
        leftFactorLteProduct prf

plusDivisorAlsoFactor : Factor n p -> Factor (n + p) p
plusDivisorAlsoFactor (CofactorExists {n} {p} q positN prf) =
        CofactorExists (S q) (lteTransitive positN $ lteAddRight n) $
            rewrite plusCommutative n p in
            rewrite multRightSuccPlus p q in
            cong {f = plus p} prf

plusDivisorNeitherFactor : NotFactor n p -> NotFactor (n + p) p
plusDivisorNeitherFactor (ProperRemExists {n} {p} q r positN remPrf) =
        ProperRemExists (S q) r (lteTransitive positN $ lteAddRight n) (
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
                    let prf =
                            replace {P = \x => x = n} (plusZeroRightNeutral (q + (d * q))) $
                            replace {P = \x => x + 0 = n} (multCommutative q (S d)) prf
                    in
                    ItIsFactor $ CofactorExists q nok prf

                (FS pr) =>
                    ItIsNotFactor $ ProperRemExists q pr nok (
                            rewrite multCommutative d q in
                            rewrite sym $ multRightSuccPlus q d in
                            prf
                        )

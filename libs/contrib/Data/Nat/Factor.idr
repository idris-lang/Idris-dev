module Data.Nat.Factor

import Data.Fin
import Data.Fin.Extra
import Data.Nat

%default total
%access public export


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

data CommonFactor : Nat -> Nat -> Nat -> Type where
    CommonFactorExists : {a, b : Nat} -> (p : Nat) -> Factor a p -> Factor b p -> CommonFactor a b p


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

Uninhabited (Factor n Z) where
    uninhabited (CofactorExists q ok prf) =
        absurd . succNotLTEzero $ replace {P = LTE 1} (sym prf) ok

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

multFactor : (p, q : Nat) -> {auto positP : LTE 1 p} -> {auto positQ : LTE 1 q} -> Factor (p * q) p
multFactor Z _ {positP} = absurd $ succNotLTEzero positP
multFactor _ Z {positQ} = absurd $ succNotLTEzero positQ
multFactor (S k) (S j) {positP} {positQ} =
        CofactorExists (S j) (LTESucc LTEZero) Refl

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

multNAlsoFactor : Factor n p -> (a : Nat) -> {auto aok : LTE 1 a} -> Factor (n * a) p
multNAlsoFactor _ Z {aok} = absurd $ succNotLTEzero aok
multNAlsoFactor (CofactorExists {n} {p} q positN prf) (S a) =
        CofactorExists (q * S a) (lteMultRight positN a) $
            rewrite sym prf in
            multAssociative p q (S a)

plusFactor : Factor n p -> Factor m p -> Factor (n + m) p
plusFactor {n} {p} nFactor@(CofactorExists qn positN prfN) (CofactorExists qm positM prfM) =
        let positP = the (LTE 1 p) $ case n of
                Z => absurd $ succNotLTEzero positN
                (S k) => nonZeroLeftFactor {a = p} {b = qn} prfN
            positQNQM = the (LTE 1 (qn + qm)) $ case qn of
                Z => absurd . succNotLTEzero .
                    replace {P = LTE 1} (multZeroRightZero p) $
                    replace {P = LTE 1} (sym prfN) positN
                (S k) => LTESucc LTEZero
        in
        rewrite sym prfN in
        rewrite sym prfM in
        rewrite sym $ multDistributesOverPlusRight p qn qm in
        multFactor p (qn + qm) {positQ = positQNQM}

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

factNotSuccFact : {n, p : Nat} -> GT p 1 -> Factor n p -> NotFactor (S n) p
factNotSuccFact {n} {p = Z} pGt1 (CofactorExists q positN prf) =
        absurd $ succNotLTEzero pGt1
factNotSuccFact {n} {p = S Z} pGt1 (CofactorExists q positN prf) =
        absurd . succNotLTEzero $ fromLteSucc pGt1
factNotSuccFact {n} {p = S (S k)} pGt1 (CofactorExists q positN prf) =
        let r = FZ in -- remember it's remainders precedessor
        ProperRemExists q r (lteSuccRight positN) (
            rewrite prf in
            rewrite plusCommutative n 1 in
            Refl
        )

oneCommonFactor : (a, b : Nat) -> {auto aok : LTE 1 a} -> {auto bok : LTE 1 b} -> CommonFactor a b 1
oneCommonFactor a b {aok} {bok} = CommonFactorExists 1
        (CofactorExists a aok (rewrite plusZeroRightNeutral a in Refl))
        (CofactorExists b bok (rewrite plusZeroRightNeutral b in Refl))

selfIsCommonFactor : (a : Nat) -> {auto ok : LTE 1 a} -> CommonFactor a a a
selfIsCommonFactor Z {ok} = absurd $ succNotLTEzero ok
selfIsCommonFactor (S k) = CommonFactorExists (S k) (selfFactor $ S k) (selfFactor $ S k)

swapCommonFactor : CommonFactor a b f -> CommonFactor b a f
swapCommonFactor (CommonFactorExists f aprf bprf) = CommonFactorExists f bprf aprf

namespace GCD
    %access private

    data Search : Type where
        SearchArgs : (a, b : Nat) -> LTE b a -> {auto bNonZero : LTE 1 b} -> Search

    left : Search -> Nat
    left (SearchArgs l _ _) = l

    right : Search -> Nat
    right (SearchArgs _ r _) = r

    Sized Search where
        size (SearchArgs a b _) = a + b

    step : (x : Search) ->
        (rec : (y : Search) -> Smaller y x ->  (f : Nat ** CommonFactor (left y) (right y) f)) ->
        (f : Nat ** CommonFactor (left x) (right x) f)
    step (SearchArgs Z _ bLteA {bNonZero}) _ = absurd . succNotLTEzero $ lteTransitive bNonZero bLteA
    step (SearchArgs _ Z _ {bNonZero}) _ = absurd $ succNotLTEzero bNonZero
    step (SearchArgs (S a) (S b) bLteA {bNonZero}) rec with (divMod (S a) (S b))
        | Fraction (S a) (S b) q FZ prf =
            let sbIsFactor = the (plus q (mult b q) = S a) $
                    rewrite multCommutative b q in
                    rewrite sym $ multRightSuccPlus q b in
                    replace {P = \x => x = S a} (plusZeroRightNeutral (q * S b)) prf
                skDividesA = CofactorExists q (lteTransitive bNonZero bLteA) sbIsFactor
                skDividesB = selfFactor (S b)
            in
            (S b ** CommonFactorExists (S b) skDividesA skDividesB)

        | Fraction (S a) (S b) q (FS r) prf =
                let rLtSb = lteSuccRight $ elemSmallerThanBound r
                    qGt1 = the (LTE 1 q) $ case q of
                        Z => absurd . notLteAndGt (S $ finToNat r) b (elemSmallerThanBound r) $
                            replace {P = LTE (S b)} (sym prf) bLteA
                        (S k) => LTESucc LTEZero
                    smaller = the (LTE (S (S (plus b (S (finToNat r))))) (S (plus a (S b)))) $
                        rewrite plusCommutative a (S b) in
                        LTESucc . LTESucc . addLteLeft . fromLteSucc $ lteTransitive (elemSmallerThanBound $ FS r) bLteA
                    (f ** CommonFactorExists f prfSb prfRem) = rec (SearchArgs (S b) (S $ finToNat r) rLtSb) smaller
                    prfSa = the (Factor (S a) f) $
                        rewrite sym prf in
                        rewrite multCommutative q (S b) in
                        plusFactor (multNAlsoFactor prfSb q) prfRem
                in
                (f ** CommonFactorExists f prfSa prfSb)

gcd : (a, b : Nat) -> {auto aok : LTE 1 a} -> {auto bok : LTE 1 b} -> (f : Nat ** CommonFactor a b f)
gcd Z _ {aok} = absurd aok
gcd _ Z {bok} = absurd bok
gcd (S a) (S b) with (cmp (S a) (S b))
    gcd (S (b + S d)) (S b) | CmpGT d =
        let aGtB = the (LTE (S b) (S (b + S d))) $
                rewrite sym $ plusSuccRightSucc b d in
                LTESucc . lteSuccRight $ lteAddRight b
        in
        sizeInd GCD.step $ GCD.SearchArgs (S (b + S d)) (S b) aGtB
    gcd (S a) (S a)         | CmpEQ =
        (S a ** selfIsCommonFactor (S a))
    gcd (S a) (S (a + S d)) | CmpLT d =
        let aGtB = the (LTE (S a) (S (plus a (S d)))) $
                rewrite sym $ plusSuccRightSucc a d in
                LTESucc . lteSuccRight $ lteAddRight a
            (f ** prf) = sizeInd GCD.step $ GCD.SearchArgs (S (a + S d)) (S a) aGtB
        in
        (f ** swapCommonFactor prf)

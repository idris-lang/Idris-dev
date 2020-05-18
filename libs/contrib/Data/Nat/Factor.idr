module Data.Nat.Factor

import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Syntax.PreorderReasoning

%default total
%access public export


||| Factor n p is a witness that p is indeed a factor of n,
||| i.e. there exists a q such that p * q = n.
data Factor : Nat -> Nat -> Type where
    CofactorExists : {n, p : Nat} -> (q : Nat) -> n = p * q -> Factor n p

||| NotFactor n p is a witness that p is NOT a factor of n,
||| i.e. there exist a q and an r, greater than 0 but smaller than p,
||| such that p * q + r = n.
data NotFactor : Nat -> Nat -> Type where
    ProperRemExists : {n, p : Nat} -> (q : Nat) ->
        (r : Fin (pred p)) ->
        n = p * q + S (finToNat r) ->
        NotFactor n p

||| DecFactor n p is a result of the process which decides
||| whether or not p is a factor on n.
data DecFactor : Nat -> Nat -> Type where
    ItIsFactor : Factor n f -> DecFactor n f
    ItIsNotFactor : NotFactor n f -> DecFactor n f

||| CommonFactor n m p is a witness that p is a factor of both n and m.
data CommonFactor : Nat -> Nat -> Nat -> Type where
    CommonFactorExists : {a, b : Nat} -> (p : Nat) -> Factor a p -> Factor b p -> CommonFactor a b p

||| GCD n m p is a witness that p is THE greatest common factor of both n and m.
||| The second argument to the constructor is a function which for all q being
||| a factor of both n and m, proves that q is a factor of p.
|||
||| This is equivalent to a more straightforward definition, stating that for
||| all q being a factor of both n and m, q is less than or equal to p, but more
||| powerful and therefore more useful for further proofs. See below for a proof
||| that if q is a factor of p then q must be less than or equal to p.
data GCD : Nat -> Nat -> Nat -> Type where
    MkGCD : {a, b, p : Nat} ->
        (CommonFactor a b p) ->
        ((q : Nat) -> CommonFactor a b q -> Factor p q) ->
        GCD a b p


||| Given a statement that p is factor of n, return its cofactor.
cofactor : Factor n p -> (q : Nat ** Factor n q)
cofactor (CofactorExists {n} {p} q prf) =
        (q ** CofactorExists p $ rewrite multCommutative q p in prf)


||| No number can simultaneously be and not be a factor of another number.
factorNotFactorAbsurd : Factor n p -> NotFactor n p -> Void
factorNotFactorAbsurd {n} {p} (CofactorExists q prf) (ProperRemExists q' r contra) with (cmp q q')
    factorNotFactorAbsurd {n} {p} (CofactorExists q prf) (ProperRemExists (q + S d) r contra) | CmpLT d =
        plusSuccIsNotIdentity {a = p * q} {b = (p * S d) + finToNat r} $
        rewrite plusSuccRightSucc (p * S d) (finToNat r) in
        rewrite plusAssociative (p * q) (p * S d) (S (finToNat r)) in
        rewrite sym $ multDistributesOverPlusRight p q (S d) in
        rewrite sym contra in
        rewrite sym prf in
        Refl
    factorNotFactorAbsurd {n} {p} (CofactorExists q prf) (ProperRemExists q r contra) | CmpEQ =
        uninhabited .
        subtractEqLeft {a = p * q} {b = S (finToNat r)} {c = 0} $
        rewrite plusZeroRightNeutral (p * q) in
        rewrite sym contra in
        prf
    factorNotFactorAbsurd {n} {p} (CofactorExists (q + S d) prf) (ProperRemExists q r contra) | CmpGT d =
        let srEQpPlusPD = the (plus p (mult p d) = S (finToNat r)) $
                rewrite sym $ multRightSuccPlus p d in
                subtractEqLeft {a = p * q} {b = p * (S d)} {c = S (finToNat r)} $
                    rewrite sym $ multDistributesOverPlusRight p q (S d) in
                    rewrite sym contra in
                    sym prf
        in
        case p of
            Z => uninhabited srEQpPlusPD
            (S k) =>
                succNotLTEzero .
                subtractLteLeft {a = k} {b = S (d + (k * d))} {c = 0} $
                rewrite sym $ plusSuccRightSucc k (d + (k * d)) in
                rewrite plusZeroRightNeutral k in
                rewrite srEQpPlusPD in
                elemSmallerThanBound r


||| The relation of common factor is symmetric, that is if p is a common factor
||| of n and m, then it is also a common factor if m and n.
commonFactorSym : CommonFactor a b p -> CommonFactor b a p
commonFactorSym (CommonFactorExists p pfa pfb) = CommonFactorExists p pfb pfa

||| 1 is a factor of any natural number.
oneIsFactor : (n : Nat) -> Factor n 1
oneIsFactor Z = CofactorExists Z Refl
oneIsFactor (S k) = CofactorExists (S k) (rewrite plusZeroRightNeutral k in Refl)

||| For all natural numbers n, n is (the greatest) a factor of n.
factorSym : (n : Nat) -> Factor n n
factorSym Z = CofactorExists 1 Refl
factorSym (S k) = CofactorExists 1 (rewrite multOneRightNeutral k in Refl)

||| If b is a factor of a and c is a factor of b, then c is also a factor of a.
factorTransitive : Factor a b -> Factor b c -> Factor a c
factorTransitive (CofactorExists qb prfAB) (CofactorExists qc prfBC) =
        CofactorExists (qb * qc) (
            rewrite prfAB in
            rewrite prfBC in
            rewrite sym $ multAssociative c qc qb in
            rewrite multCommutative qc qb in
            Refl
        )

||| Anything is a factor of 0.
factorZeroAnything : (a : Nat) -> Factor 0 a
factorZeroAnything a = CofactorExists 0 (sym $ multZeroRightZero a)

||| For all natural numbers p and q, p is a factor of (p * q).
multFactor : (p, q : Nat) -> Factor (p * q) p
multFactor p q = CofactorExists q Refl

||| If n > 0 then any factor of n must be less than or equal to n.
factorLteNumber : Factor n p -> {auto positN : LTE 1 n} -> LTE p n
factorLteNumber (CofactorExists {n} {p} Z prf) {positN} =
        let nIsZero = replace {P = \x => n = x} (multZeroRightZero p) prf
            oneLteZero = replace {P = LTE 1} nIsZero positN
        in
        absurd $ succNotLTEzero oneLteZero
factorLteNumber (CofactorExists {n} {p} (S k) prf) =
        leftFactorLteProduct $ sym prf

||| If p is a factor of n, then it is also a factor of (n + p).
plusDivisorAlsoFactor : Factor n p -> Factor (n + p) p
plusDivisorAlsoFactor (CofactorExists {n} {p} q prf) =
        CofactorExists (S q) $
            rewrite plusCommutative n p in
            rewrite multRightSuccPlus p q in
            cong {f = plus p} prf

||| If p is NOT a factor of n, then it also is NOT a factor of (n + p).
plusDivisorNeitherFactor : NotFactor n p -> NotFactor (n + p) p
plusDivisorNeitherFactor (ProperRemExists {n} {p} q r remPrf) =
        ProperRemExists (S q) r $
            rewrite multRightSuccPlus p q in
            rewrite sym $ plusAssociative p (p * q) (S $ finToNat r) in
            rewrite plusCommutative p ((p * q) + S (finToNat r)) in
            rewrite remPrf in
            Refl

||| If p is a factor of n, then it is also a factor of any multiply of n.
multNAlsoFactor : Factor n p -> (a : Nat) -> {auto aok : LTE 1 a} -> Factor (n * a) p
multNAlsoFactor _ Z {aok} = absurd $ succNotLTEzero aok
multNAlsoFactor (CofactorExists {n} {p} q prf) (S a) =
        CofactorExists (q * S a) $
            rewrite prf in
            sym $ multAssociative p q (S a)

||| If p is a factor of both n and m, then it is also a factor of their sum.
plusFactor : Factor n p -> Factor m p -> Factor (n + m) p
plusFactor {n} {p} (CofactorExists qn prfN) (CofactorExists qm prfM) =
        rewrite prfN in
        rewrite prfM in
        rewrite sym $ multDistributesOverPlusRight p qn qm in
        multFactor p (qn + qm)

||| If p is a factor of a sum (n + m) and a factor of n, then it is also
||| a factor of m. This could be expressed more naturally with minus, but
||| it would be more difficult to prove, since minus lacks certain properties
||| that one would expect from decent subtraction.
minusFactor : Factor (a + b) p -> Factor a p -> Factor b p
minusFactor {a} {b} (CofactorExists qab prfAB) (CofactorExists qa prfA) =
        CofactorExists (minus qab qa) (
            rewrite multDistributesOverMinusRight p qab qa in
            rewrite sym prfA in
            rewrite sym prfAB in
            (b) ={ sym $ minusZeroRight b }=
            (minus b 0) ={ sym $ plusMinusLeftCancel a b 0 }=
            (minus (a + b) (a + 0)) ={ replace {P = \x => minus (a + b) (a + 0) = minus (a + b) x} (plusZeroRightNeutral a) Refl }=
            (minus (a + b) a) QED
        )

||| If p is a common factor of a and b, then it is also a factor of their GCD.
||| This actually follows directly from the definition of GCD.
commonFactorAlsoFactorOfGCD : Factor a p -> Factor b p -> GCD a b q -> Factor q p
commonFactorAlsoFactorOfGCD {p} pfa pfb (MkGCD _ greatest) =
        greatest p (CommonFactorExists p pfa pfb)


||| A decision procedure for whether of not p is a factor of n.
decFactor : (n, d : Nat) -> DecFactor n d
decFactor n Z = ?whaatIfZ
decFactor n (S d) with (Data.Fin.Extra.divMod n (S d))
        | (Fraction n (S d) q r prf) = case r of
                FZ =>
                    let prf =
                            replace {P = \x => x = n} (plusZeroRightNeutral (q + (d * q))) $
                            replace {P = \x => x + 0 = n} (multCommutative q (S d)) prf
                    in
                    ItIsFactor $ CofactorExists q (sym prf)

                (FS pr) =>
                    ItIsNotFactor $ ProperRemExists q pr (
                            rewrite multCommutative d q in
                            rewrite sym $ multRightSuccPlus q d in
                            sym prf
                        )

||| For all p greater than 1, if p is a factor of n, then it is NOT a factor
||| of (n + 1).
factNotSuccFact : {n, p : Nat} -> GT p 1 -> Factor n p -> NotFactor (S n) p
factNotSuccFact {n} {p = Z} pGt1 (CofactorExists q prf) =
        absurd $ succNotLTEzero pGt1
factNotSuccFact {n} {p = S Z} pGt1 (CofactorExists q prf) =
        absurd . succNotLTEzero $ fromLteSucc pGt1
factNotSuccFact {n} {p = S (S k)} pGt1 (CofactorExists q prf) =
        let r = FZ in -- remember it's remainders precedessor
        ProperRemExists q r (
            rewrite sym prf in
            rewrite plusCommutative n 1 in
            Refl
        )

||| 1 is a common factor of any pair of natural numbers.
oneCommonFactor : (a, b : Nat) -> CommonFactor a b 1
oneCommonFactor a b = CommonFactorExists 1
        (CofactorExists a (rewrite plusZeroRightNeutral a in Refl))
        (CofactorExists b (rewrite plusZeroRightNeutral b in Refl))

||| Any natural number is a common factor of itself and itself.
selfIsCommonFactor : (a : Nat) -> {auto ok : LTE 1 a} -> CommonFactor a a a
selfIsCommonFactor Z {ok} = absurd $ succNotLTEzero ok
selfIsCommonFactor (S k) = CommonFactorExists (S k) (factorSym $ S k) (factorSym $ S k)

-- Some helper definitions only for internal use of gcd procedure.
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
        (rec : (y : Search) -> Smaller y x ->  (f : Nat ** GCD (left y) (right y) f)) ->
        (f : Nat ** GCD (left x) (right x) f)
    step (SearchArgs Z _ bLteA {bNonZero}) _ = absurd . succNotLTEzero $ lteTransitive bNonZero bLteA
    step (SearchArgs _ Z _ {bNonZero}) _ = absurd $ succNotLTEzero bNonZero
    step (SearchArgs (S a) (S b) bLteA {bNonZero}) rec with (divMod (S a) (S b))
        | Fraction (S a) (S b) q FZ prf =
            let sbIsFactor = the (S a = plus q (mult b q)) $
                    rewrite multCommutative b q in
                    rewrite sym $ multRightSuccPlus q b in
                    replace {P = \x => S a = x} (plusZeroRightNeutral (q * S b)) $ sym prf
                skDividesA = CofactorExists q sbIsFactor
                skDividesB = factorSym (S b)
                greatest = \q', (CommonFactorExists q' _ qfb) => qfb
            in
            (S b ** MkGCD (CommonFactorExists (S b) skDividesA skDividesB) greatest)

        | Fraction (S a) (S b) q (FS r) prf =
                let rLtSb = lteSuccRight $ elemSmallerThanBound r
                    qGt1 = the (LTE 1 q) $ case q of
                        Z => absurd . notLteAndGt (S $ finToNat r) b (elemSmallerThanBound r) $
                            replace {P = LTE (S b)} (sym prf) bLteA
                        (S k) => LTESucc LTEZero
                    smaller = the (LTE (S (S (plus b (S (finToNat r))))) (S (plus a (S b)))) $
                        rewrite plusCommutative a (S b) in
                        LTESucc . LTESucc . addLteLeft . fromLteSucc $ lteTransitive (elemSmallerThanBound $ FS r) bLteA
                    (f ** MkGCD (CommonFactorExists f prfSb prfRem) greatestSbSr) =
                        rec (SearchArgs (S b) (S $ finToNat r) rLtSb) smaller
                    prfSa = the (Factor (S a) f) $
                        rewrite sym prf in
                        rewrite multCommutative q (S b) in
                        plusFactor (multNAlsoFactor prfSb q) prfRem
                    greatest = \q', (CommonFactorExists q' qfa qfb) =>
                        let sbfqSb =
                                the (Factor (q * S b) (S b)) $
                                rewrite multCommutative q (S b) in
                                multFactor (S b) q
                            rightPrf = minusFactor {a = q * S b} {b = S (finToNat r)}
                                (rewrite prf in qfa)
                                (factorTransitive sbfqSb qfb)
                        in
                        greatestSbSr q' (CommonFactorExists q' qfb rightPrf)
                in
                (f ** MkGCD (CommonFactorExists f prfSa prfSb) greatest)

||| An implementation of Euclidean Algorithm for computing greatest common
||| divisors. It is proven correct and total; returns a proof that computed
||| number actually IS the GCD. Unfortunately it's very slow, so improvements
||| in terms of efficiency would be welcome.
export
gcd : (a, b : Nat) -> {auto ok : NotBothZero a b} -> (f : Nat ** GCD a b f)
gcd Z Z impossible
gcd Z b =
    (b ** MkGCD (CommonFactorExists b (factorZeroAnything b) (factorSym b)) $
        \q, (CommonFactorExists q _ prf) => prf
    )
gcd a Z =
    (a ** MkGCD (CommonFactorExists a (factorSym a) (factorZeroAnything a)) $
        \q, (CommonFactorExists q prf _) => prf
    )
gcd (S a) (S b) with (cmp (S a) (S b))
    gcd (S (b + S d)) (S b) | CmpGT d =
        let aGtB = the (LTE (S b) (S (b + S d))) $
                rewrite sym $ plusSuccRightSucc b d in
                LTESucc . lteSuccRight $ lteAddRight b
        in
        sizeInd GCD.step $ GCD.SearchArgs (S (b + S d)) (S b) aGtB
    gcd (S a) (S a)         | CmpEQ =
        let greatest = \q, (CommonFactorExists q qfa _) => qfa in
        (S a ** MkGCD (selfIsCommonFactor (S a)) greatest)
    gcd (S a) (S (a + S d)) | CmpLT d =
        let aGtB = the (LTE (S a) (S (plus a (S d)))) $
                rewrite sym $ plusSuccRightSucc a d in
                LTESucc . lteSuccRight $ lteAddRight a
            (f ** MkGCD prf greatest) = sizeInd GCD.step $ GCD.SearchArgs (S (a + S d)) (S a) aGtB
        in
        (f ** MkGCD (commonFactorSym prf) (\q, cf => greatest q $ commonFactorSym cf))

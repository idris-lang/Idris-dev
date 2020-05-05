module Data.Nat.Factor

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
    ProperRemExists : (n, p, q, r : Nat) ->
        LTE 1 n ->
        {auto rltp : LT (S r) p} ->
        p * q + S r = n ->
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

aPlusSBNotA : {a, b : Nat} -> a + S b = a -> Void
aPlusSBNotA {a = Z} {b} prf = absurd prf
aPlusSBNotA {a = (S k)} {b} prf =
        aPlusSBNotA $ succInjective (k + S b) k prf
--
factPairNotFactPairAbsurd : FactorsOf n (p, q) -> NotFactorsOf n (p, q) -> Void
factPairNotFactPairAbsurd (FactorPair n p q _ prf) (NotFactorPair _ _ _ r _ contra) =
        aPlusSBNotA $ replace {P = \a => a + S r = n} prf contra


factorNotFactorAbsurd : Factor n p -> NotFactor n p -> Void
factorNotFactorAbsurd (CoFactorExists q (FactorPair n p q positN prf)) (ProperRemExists n p q' r _ contra {rltp}) =
        thisIsAbsurd q q' $ replace {P = \x => (p * q') + S r = x} (sym prf) contra
    where
    thisIsAbsurd : (q, q' : Nat) -> (p * q') + S r = p * q -> Void
    thisIsAbsurd q q' a with (cmp q q')
        thisIsAbsurd q (q + S d) a  | CmpLT d =
            aPlusSBNotA .
            replace {P = \x => (p * q) + x = p * q} (sym $ plusSuccRightSucc (p * S d) r) .
            replace {P = \x => x = p * q} (sym $ plusAssociative (p * q) (p * S d) (S r)) $
            replace {P = \x => x + S r = p * q} (multDistributesOverPlusRight p q (S d)) a
        thisIsAbsurd q q a          | CmpEQ = aPlusSBNotA a
        thisIsAbsurd (q + S d) q a  | CmpGT d =
            let defSr =
                    replace {P = \x => S r = x} (multRightSuccPlus p d) .
                    subtractEqLeft $
                    replace {P = \x => (p * q) + S r = x} (multDistributesOverPlusRight p q (S d)) a
            in
            succNotLTEzero . subtractLteLeft .
            replace {P = \x => LTE (p + S (p * d)) x} (sym $ plusZeroRightNeutral p) .
            replace {P = \x => LTE x p} (plusSuccRightSucc p (p * d)) $
            replace {P = \x => LTE (S x) p} defSr rltp


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
plusDivisorNeitherFactor (ProperRemExists n p q r positN remPrf {rltp}) =
        ProperRemExists (n + p) p (S q) r (lteTransitive positN $ lteAddRight n) (
                rewrite multRightSuccPlus p q in
                rewrite sym $ plusAssociative p (p * q) (S r) in
                rewrite plusCommutative p ((p * q) + S r) in
                rewrite remPrf in
                Refl
            )
            {rltp = rltp}

decFactor : (n, d : Nat) -> LTE 1 n-> DecFactor n d
decFactor n d positN with (cmp n d)
    decFactor n (n + S x) positN  | CmpLT x = case n of
            S k =>
                ItIsNotFactor $ ProperRemExists (S k) (S k + S x) Z k positN (
                        rewrite multZeroRightZero (k + S x) in
                        Refl
                    ) {rltp = rewrite plusSuccRightSucc k (S x) in
                        rewrite sym $ plusZeroRightNeutral k in
                        rewrite plusSuccRightSucc k 0 in
                        rewrite plusSuccRightSucc k 1 in
                        rewrite plusZeroRightNeutral k in
                        addLteLeft . LTESucc $ LTESucc LTEZero
                    }
    decFactor n n positN          | CmpEQ = case n of
            S k => ItIsFactor $ selfFactor (S k)
    decFactor (d + S x) d positN  | CmpGT x =
            case assert_total $ decFactor (S x) d (LTESucc LTEZero) of
                ItIsFactor fprf => ItIsFactor (
                        rewrite plusCommutative d (S x) in
                        plusDivisorAlsoFactor fprf
                    )
                ItIsNotFactor fcontra => ItIsNotFactor (
                        rewrite plusCommutative d (S x) in
                        plusDivisorNeitherFactor fcontra
                    )

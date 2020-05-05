module Data.Nat

import Syntax.PreorderReasoning

%default total
%access public export

diff : Nat -> Nat -> Nat
diff k Z = k
diff Z j = j
diff (S k) (S j) = diff k j

succPred : (n : Nat) -> {auto ok : LTE 1 n} -> S (pred n) = n
succPred Z {ok} = absurd $ succNotLTEzero ok
succPred (S k) {ok} = Refl

plusSuccIsNotIdentity : {a, b : Nat} -> a + S b = a -> Void
plusSuccIsNotIdentity {a = Z} {b} prf = absurd prf
plusSuccIsNotIdentity {a = (S k)} {b} prf =
        plusSuccIsNotIdentity $ succInjective (k + S b) k prf

lteToSucc : LTE 1 n -> (m : Nat ** n = S m)
lteToSucc {n = Z} prf impossible
lteToSucc {n = S k} prf = (k ** Refl)

ltePlus : LTE m1 n1 -> LTE m2 n2 -> LTE (m1 + m2) (n1 + n2)
ltePlus {n1=Z} LTEZero lte = lte
ltePlus {n1=S k} LTEZero lte = lteSuccRight $ ltePlus {n1=k} LTEZero lte
ltePlus (LTESucc lte1) lte2 = LTESucc $ ltePlus lte1 lte2

lteCongPlus : (k : Nat) -> LTE m n -> LTE (m + k) (n + k)
lteCongPlus k lte = ltePlus lte lteRefl

lteMult : LTE m1 n1 -> LTE m2 n2 -> LTE (m1 * m2) (n1 * n2)
lteMult LTEZero _ = LTEZero
lteMult {m1=S k} (LTESucc _) LTEZero = rewrite multZeroRightZero k in LTEZero
lteMult (LTESucc lte1) (LTESucc lte2) = LTESucc $ ltePlus lte2 $ lteMult lte1 $ LTESucc lte2

lteCongMult : (k : Nat) -> LTE m n -> LTE (m * k) (n * k)
lteCongMult k lte = lteMult lte lteRefl

addLteRight : LTE a b -> LTE (a + c) (b + c)
addLteRight {a} {b} {c = Z} prf =
        rewrite plusZeroRightNeutral a in
        rewrite plusZeroRightNeutral b in
        prf
addLteRight {a} {b} {c = S k} prf =
        rewrite sym $ plusSuccRightSucc a k in
        rewrite sym $ plusSuccRightSucc b k in
        LTESucc $ addLteRight prf

addLteLeft : LTE b c -> LTE (a + b) (a + c)
addLteLeft {a = Z} {b} {c} prf = prf
addLteLeft {a = S k} {b} {c} prf =
        LTESucc $ addLteLeft prf

subtractLteLeft : LTE (a + b) (a + c) -> LTE b c
subtractLteLeft {a = Z} {b} {c} prf = prf
subtractLteLeft {a = S j} {b} {c} prf = subtractLteLeft $ fromLteSucc prf

subtractEqLeft : {a, b, c : Nat} -> a + b = a + c -> b = c
subtractEqLeft {a = Z} prf = prf
subtractEqLeft {a = S k} {b} {c} prf = subtractEqLeft $ succInjective (k + b) (k + c) prf

subtractEqRight : {a, b, c : Nat} -> a + c = b + c -> a = b
subtractEqRight {a} {b} {c = Z} prf =
        rewrite sym $ plusZeroRightNeutral a in
        rewrite sym $ plusZeroRightNeutral b in
        prf
subtractEqRight {a} {b} {c = S k} prf =
        subtractEqRight $
        succInjective (a + k) (b + k) .
        replace {P = \x => S (a + k) = x} (sym $ plusSuccRightSucc b k) $
        replace {P = \x => x = b + S k} (sym $ plusSuccRightSucc a k) prf

leftFactorLteProduct : a * S b = c -> LTE a c
leftFactorLteProduct {a} {b} {c} prf =
    let cGteA =
        (c) ={ sym prf }=
        (a * (S b)) ={ multRightSuccPlus a b }=
        (a + a * b) QED
    in
    rewrite cGteA in
    lteAddRight a

rightFactorLteProduct : S a * b = c -> LTE b c
rightFactorLteProduct {a} {b} {c} prf =
    leftFactorLteProduct {a = b} {b = a} $
        rewrite multRightSuccPlus b a in
        rewrite multCommutative b a in
        prf

nonZeroProdNonZeroFactors : (a, b : Nat) -> LTE 1 (S a * S b)
nonZeroProdNonZeroFactors a b = LTESucc LTEZero

nonZeroLeftFactor : {a, b : Nat} -> a * b = S n -> LTE 1 a
nonZeroLeftFactor {a = Z} eq = void . SIsNotZ $ sym eq
nonZeroLeftFactor {a = S k} _ = LTESucc LTEZero

nonZeroRightFactor : {a, b : Nat} -> a * b = S n -> LTE 1 b
nonZeroRightFactor {a} {b = Z} eq {n} =
        void . SIsNotZ $ replace (multZeroRightZero a) (sym eq)
nonZeroRightFactor {b = S k} prf = LTESucc LTEZero

module Data.Nat

%default total
%access public export

diff : Nat -> Nat -> Nat
diff k Z = k
diff Z j = j
diff (S k) (S j) = diff k j

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

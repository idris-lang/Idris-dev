module simple

import Data.Vect

plus_comm : (n : Nat) -> (m : Nat) -> (n + m = m + n)

-- Base case
-- (Z + m = m + Z) <== plus_comm = -- broken by typecase check
plus_comm Z m =
    rewrite ((m + Z = m) <== plusZeroRightNeutral) ==>
            (Z + m = m) in Refl

-- Step case
-- (S k + m = m + S k) <== plus_comm =
plus_comm (S len) m =
    rewrite ((len + m = m + len) <== plus_comm) in
    rewrite ((S (m + len) = m + S len) <== plusSuccRightSucc) in
        Refl
-- QED

append : Vect n a -> Vect m a -> Vect (m + n) a
append []        ys ?= ys
append (x :: xs) ys ?= x :: append xs ys



---------- Proofs ----------

simple.append_lemma_2 = proof {
  intros;
  compute;
  rewrite (plusSuccRightSucc m len);
  trivial;
}

simple.append_lemma_1 = proof {
  intros;
  compute;
  rewrite sym (plusZeroRightNeutral m);
  exact value;
}

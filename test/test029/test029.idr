module simple

plus_comm : (n : Nat) -> (m : Nat) -> (n + m = m + n)

-- Base case
(Z + m = m + Z) <== plus_comm =
    rewrite ((m + Z = m) <== plusZeroRightNeutral) ==>
            (Z + m = m) in refl

-- Step case
(S k + m = m + S k) <== plus_comm =
    rewrite ((k + m = m + k) <== plus_comm) in
    rewrite ((S (m + k) = m + S k) <== plusSuccRightSucc) in
        refl
-- QED

append : Vect n a -> Vect m a -> Vect (m + n) a
append []        ys ?= ys
append (x :: xs) ys ?= x :: append xs ys



---------- Proofs ----------

simple.append_lemma_2 = proof {
  intros;
  compute;
  rewrite (plusSuccRightSucc m n);
  trivial;
}

simple.append_lemma_1 = proof {
  intros;
  compute;
  rewrite sym (plusZeroRightNeutral m);
  exact value;
}


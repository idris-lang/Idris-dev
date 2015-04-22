module views

data Parity : Nat -> Type where
   Even : Parity (n + n)
   Odd  : Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity Z     = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | Even ?= Even {n=S j}
  parity (S (S (S (j + j)))) | Odd  ?= Odd {n=S j}

natToBin : Nat -> List Bool
natToBin Z = Nil
natToBin k with (parity k)
   natToBin (j + j)     | Even = False :: natToBin j
   natToBin (S (j + j)) | Odd  = True  :: natToBin j


---------- Proofs ----------

views.parity_lemma_2 = proof {
    intro;
    intro;
    rewrite sym (plusSuccRightSucc j j);
    trivial;
}

views.parity_lemma_1 = proof {
    intro;
    intro;
    rewrite sym (plusSuccRightSucc j j);
    trivial;
}



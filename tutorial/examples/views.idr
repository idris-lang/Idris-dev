module views

data Parity : Nat -> Set where
   even : Parity (n + n)
   odd  : Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity O     = even {n=O}
parity (S O) = odd {n=O}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | even ?= even {n=S j}
  parity (S (S (S (j + j)))) | odd  ?= odd {n=S j}

natToBin : Nat -> List Bool
natToBin O = Nil
natToBin k with (parity k)
   natToBin (j + j)     | even = False :: natToBin j
   natToBin (S (j + j)) | odd  = True  :: natToBin j


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



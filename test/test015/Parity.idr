module Parity

data Parity : Nat -> Type where
   even : Parity (n + n)
   odd  : Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity O     = even {n=O}
parity (S O) = odd {n=O}
parity (S (S k)) with (parity k)
    parity (S (S (j + j)))     | even ?= even {n=S j}
    parity (S (S (S (j + j)))) | odd  ?= odd {n=S j}


parity_lemma_2 = proof {
    intro;
    intro;
    rewrite sym (plusSuccRightSucc j j);
    trivial;
}

parity_lemma_1 = proof {
    intro j;
    intro;
    rewrite sym (plusSuccRightSucc j j);
    trivial;
}


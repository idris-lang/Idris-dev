module Parity

data Parity : Nat -> Type where
    even : {n : Nat} -> Parity (n + n)
    odd  : {n : Nat} -> Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity Z     = even {n=Z}
parity (S Z) = odd {n=Z}
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


module Parity

%access public export

data Parity : Nat -> Type where
    Even : {n : Nat} -> Parity (n + n)
    Odd  : {n : Nat} -> Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity Z     = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
    parity (S (S (j + j)))     | Even ?= Even {n=S j}
    parity (S (S (S (j + j)))) | Odd  ?= Odd {n=S j}


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


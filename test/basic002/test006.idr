module Main

data Parity : Nat -> Type where
    Even : {n : Nat} -> Parity (n + n)
    Odd  : {n : Nat} -> Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity Z     = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | (Even {n = j}) ?= Even {n=S j}
  parity (S (S (S (j + j)))) | (Odd {n = j})  ?= Odd {n=S j}

natToBin : Nat -> List Bool
natToBin Z = Nil
natToBin k with (parity k)
   natToBin (j + j)     | Even {n = j} = False :: natToBin j
   natToBin (S (j + j)) | Odd {n = j}  = True  :: natToBin j

main : IO ()
main = do printLn (natToBin 42)

---------- Proofs ----------

Main.parity_lemma_2 = proof {
    intro j;
    intro;
    rewrite sym (plusSuccRightSucc j j);
    trivial;
};

Main.parity_lemma_1 = proof {
    intro j;
    intro;
    rewrite sym (plusSuccRightSucc j j);
    trivial;
};


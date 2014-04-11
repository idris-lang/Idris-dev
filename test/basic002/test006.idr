module Main

data Parity : Nat -> Type where
    even : {n : Nat} -> Parity (n + n)
    odd  : {n : Nat} -> Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity Z     = even {n=Z}
parity (S Z) = odd {n=Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | (even {n = j}) ?= even {n=S j}
  parity (S (S (S (j + j)))) | (odd {n = j})  ?= odd {n=S j}

natToBin : Nat -> List Bool
natToBin Z = Nil
natToBin k with (parity k)
   natToBin (j + j)     | even {n = j} = False :: natToBin j
   natToBin (S (j + j)) | odd {n = j}  = True  :: natToBin j

main : IO ()
main = do print (natToBin 42)

---------- Proofs ----------

Main.parity_lemma_2 = proof {
    intro;
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


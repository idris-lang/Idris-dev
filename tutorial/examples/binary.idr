module main

data Binary : Nat -> Set where
    bEnd : Binary O
    bO : Binary n -> Binary (n + n)
    bI : Binary n -> Binary (S (n + n))

instance Show (Binary n) where
    show (bO x) = show x ++ "0"
    show (bI x) = show x ++ "1"
    show bEnd = ""

data Parity : Nat -> Set where
   even : Parity (n + n)
   odd  : Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity O     = even {n=O}
parity (S O) = odd {n=O}
parity (S (S k)) with (parity k)
    parity (S (S (j + j)))     | even ?= even {n=S j}
    parity (S (S (S (j + j)))) | odd  ?= odd {n=S j}

natToBin : (n:Nat) -> Binary n
natToBin O = bEnd
natToBin (S k) with (parity k)
   natToBin (S (j + j))     | even  = bI (natToBin j)
   natToBin (S (S (j + j))) | odd  ?= bO (natToBin (S j))

intToNat : Int -> Nat
intToNat 0 = O
intToNat x = if (x>0) then (S (intToNat (x-1))) else O

main : IO ()
main = do putStr "Enter a number: "
          x <- getLine
          print (natToBin (fromInteger (cast x)))

---------- Proofs ----------

natToBin_lemma_1 = proof {
    intro;
    intro;
    rewrite sym (plusSuccRightSucc j j);
    trivial;
}

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



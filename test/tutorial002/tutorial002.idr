module Main

data Binary : Nat -> Type where
    bEnd : Binary Z
    bO : Binary n -> Binary (n + n)
    bI : Binary n -> Binary (S (n + n))

instance Show (Binary n) where
    show (bO x) = show x ++ "0"
    show (bI x) = show x ++ "1"
    show bEnd = ""

data Parity : Nat -> Type where
   even : Parity (n + n)
   odd  : Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity Z     = even {n=Z}
parity (S Z) = odd {n=Z}
parity (S (S k)) with (parity k)
    parity (S (S (j + j)))     | even ?= even {n=S j}
    parity (S (S (S (j + j)))) | odd  ?= odd {n=S j}

natToBin : (n:Nat) -> Binary n
natToBin Z = bEnd
natToBin (S k) with (parity k)
   natToBin (S (j + j))     | even  = bI (natToBin j)
   natToBin (S (S (j + j))) | odd  ?= bO (natToBin (S j))

intToNat : Int -> Nat
intToNat 0 = Z
intToNat x = if (x>0) then (S (intToNat (x-1))) else Z

main : IO ()
main = do putStr "Enter a number: "
          x <- getLine
          print (natToBin (fromInteger (cast x)))

---------- Proofs ----------

Main.natToBin_lemma_1 = proof
  intros
  rewrite plusSuccRightSucc j j
  rewrite sym (plusSuccRightSucc j j)
  trivial


parity_lemma_1 = proof
    intros
    rewrite sym (plusSuccRightSucc j j)
    trivial


parity_lemma_2 = proof {
    intro;
    intro;
    rewrite sym (plusSuccRightSucc j j);
    trivial;
}



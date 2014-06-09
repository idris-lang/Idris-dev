
data Parity : Nat -> Type where
   even : Parity (n + n)
   odd  : Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity Z     = even {n=Z}
parity (S Z) = odd {n=Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | even = even {n=S j}
  parity (S (S (S (j + j)))) | odd  = odd {n=S j}


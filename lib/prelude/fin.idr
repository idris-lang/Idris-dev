module prelude.fin

import prelude.nat

data Fin : Nat -> Set where
    fO : Fin (S k)
    fS : Fin k -> Fin (S k)

instance Eq (Fin n) where
   fO == fO = True
   (fS k) == (fS k') = k == k'
   _ == _ = False


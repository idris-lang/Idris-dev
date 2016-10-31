module Data.Fin.Extra

import Data.Fin

||| Proof that an element **n** of Fin **m** , when converted to Nat is smaller than the bound **m**.
public export
elemSmallerThanBound : (n : Fin m) -> LTE (finToNat n) m
elemSmallerThanBound FZ = LTEZero
elemSmallerThanBound (FS x) = LTESucc (elemSmallerThanBound x)

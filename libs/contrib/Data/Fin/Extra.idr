module Data.Fin.Extra

import Data.Fin


elemSmallerThanBound : (n : Fin m) -> LTE (finToNat n) m
elemSmallerThanBound FZ = LTEZero
elemSmallerThanBound (FS x) = LTESucc (elemSmallerThanBound x)

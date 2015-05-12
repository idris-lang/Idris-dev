||| Test that explicit proof objects on the with rule work
module Cmp


data MyCmp : Nat -> Nat -> Type where
  IsLT : (d : Nat) -> MyCmp n         (S d + n)
  IsEQ :              MyCmp n         n
  IsGT : (d : Nat) -> MyCmp (S d + n) n

myCmp : (j, k : Nat) -> MyCmp j k
myCmp Z     Z     = IsEQ
myCmp Z     (S k) = rewrite sym $ plusZeroRightNeutral k in IsLT k
myCmp (S j) Z     = rewrite sym $ plusZeroRightNeutral j in IsGT j
myCmp (S j) (S k) with (myCmp j k) proof p
  myCmp (S j) (S (S (plus d j))) | (IsLT d) = rewrite plusSuccRightSucc d j
                                              in let useless = id p in IsLT d
  myCmp (S j)              (S j) | IsEQ = IsEQ
  myCmp (S (S (plus d k))) (S k) | (IsGT d) = rewrite plusSuccRightSucc d k
                                              in IsGT d

%default total

data PP : Type where
  MkPP : Int -> PP

data TT' : Nat -> Type where
  T1 : TT' 0
  T2 : (n : Nat) -> TT' (S n)

data TT'' : Int -> Type where
  T1' : TT'' 0
  T2' : (n : Int) -> TT'' (n + 1)

data TTPP : Type where
  MkTTPP : PP -> PP -> TTPP


g1 : TT' n -> TT' n -> Bool
g1 T1 T1 = True
g1 (T2 Z) (T2 Z) = True
g1 (T2 (S Z)) (T2 (S Z)) = True
g1 (T2 (S (S Z))) (T2 (S (S Z))) = True

g2 : TT'' n -> TT'' n -> Bool
g2 T1' T1' = True
g2 (T2' 0) (T2' 0) = True
g2 (T2' 1) (T2' 1) = True
g2 (T2' 2) (T2' 2) = True

g3 : TT'' n -> Bool
g3 T1' = True
g3 (T2' 0) = True
g3 (T2' 1) = True
g3 (T2' 2) = True

g4 : TTPP -> Bool
g4 (MkTTPP (MkPP 0) (MkPP 0)) = True
g4 (MkTTPP (MkPP 1) (MkPP 1)) = True
g4 (MkTTPP (MkPP 2) (MkPP n)) = True
    
f' : Int -> Bool
f' 0 = True
f' 1 = True
f' 2 = True

f : PP -> Bool
f (MkPP 0) = True
f (MkPP 1) = True
f (MkPP 2) = True

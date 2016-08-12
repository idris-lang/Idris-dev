%default total

data TS : Type where
  T1 : TS
  T2 : TS
  T3 : TS

data TP : Type where
  MkTP : TS -> TS -> TP

data TP2 : Type where
  MkTP2 : (TS, TS) -> TP2

f1 : TP -> Bool
f1 (MkTP T1 x) = True
f1 (MkTP x T1) = True

f2 : (TP, TS) -> Bool
f2 (MkTP T1 x, _) = True
f2 (MkTP x T1, _) = True

f3 : ((TP, TS), TS) -> Bool
f3 ((MkTP T1 x, _), _) = True
f3 ((MkTP x T1, _), _) = True

g1 : TS -> TS -> Bool
g1 T1 x = True
g1 x T1 = True

g2 : (TS, TS) -> Bool
g2 (T1, x) = True
g2 (y, T1) = True

h1 : Bool -> Bool -> Bool
h1 True x = True
h1 x True = True

h2 : (Bool, Bool) -> Bool
h2 (True, x) = True
h2 (y, True) = True

h3 : TP2 -> Bool
h3 (MkTP2 (T1, x)) = True
h3 (MkTP2 (x, T1)) = True

h4 : (TP2, TS) -> TS -> Bool
h4 (MkTP2 (T1, x), _) _ = True
h4 (MkTP2 (x, T1), _) _ = True

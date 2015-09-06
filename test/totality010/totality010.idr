%default total

%default total
succNotLTE' : (LTE (S x) x) -> Void
succNotLTE' {x = Z} prf = succNotLTEzero prf
succNotLTE' {x = (S k)} (LTESucc prf) = succNotLTE' prf

succNotLTE : Not (LTE (S x) x)
succNotLTE = succNotLTE'

succNotLTE2 : Not (LTE (S x) x)
succNotLTE2 {x = Z} prf = succNotLTEzero prf
succNotLTE2 {x = (S k)} (LTESucc prf) = succNotLTE prf

-- a defective even-odd definition allows me to prove bottom

mutual
  data Even : Nat -> Type where
    ZeroEven : Even Z
    MkEven : Odd n -> Even (S n)
    MkBad  : Even n -> Even (S n)

  data Odd : Nat -> Type where
    MkOdd : Even n -> Odd (S n)

evenNotS : Even n -> Not (Even (S n))
evenNotS MkEven ZeroEven impossible

bad : Void
bad = evenNotS ZeroEven $ MkBad ZeroEven


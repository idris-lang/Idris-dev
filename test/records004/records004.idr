module Main

-- Old-style records

||| The type A.
record A : Type -> Type where
  ||| Construct A.
  ||| @ n the number
  ||| @ xs the vector
  MkA : (n : Nat) -> (xs : Vect n Nat) -> A a

-- New-style records, simple.

||| The type B.
||| @ a The contained type.
record B : (a : Type) -> Type where
  constructor MkB

  ||| The number.
  n : Nat

  ||| The vector.
  xs : Vect n a

-- New-style records, full-featured.

||| The type C.
||| @ a An implicit param.
||| @ n An explicit param.
record C : {a : Type} -> (n : Nat) -> Type where
  constructor MkC

  ||| A rather unhelpful implicit because it can't be inferred.
  {unhelpfulField : a}

  ||| The wrapped vector.
  xs : Vect n a

rA : A Bool
rA = MkA 2 [0,1]

rB : B Int
rB = MkB _ 3 [4,1,2]

rC : C {a = Bool} 4
rC = MkC _ {unhelpfulField = True} [True, False, False, True]

main : IO ()
main = do
  print $ record { n } rA
  print $ record { xs } rA
  print $ record { n } rB
  print $ record { xs } rB
  print $ record { n } rC
  print $ record { xs } rC

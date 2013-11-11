module Test

X : Nat -> Type
X t = (c : Nat ** so (c < 5))

column : X t -> Nat
column = getWitness

data Action = Left | Ahead | Right

admissible : X t -> Action -> Bool
admissible x Ahead = column x == 0 || column x == 4
admissible x Left  = column x <= 2
admissible x Right = column x >= 2

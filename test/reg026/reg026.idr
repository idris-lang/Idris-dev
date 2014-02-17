module Test

X : Nat -> Type
X t = (c : Nat ** so (c < 5))

column : X t -> Nat
column = getWitness

data Action = Left | Ahead | Right

admissible : X t -> Action -> Bool
admissible {t} x Ahead = column {t} x == 0 || column {t} x == 4
admissible {t} x Left  = column {t} x <= 2
admissible {t} x Right = column {t} x >= 2

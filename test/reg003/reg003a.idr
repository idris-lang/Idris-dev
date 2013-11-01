
data EvenList : Type where
    ENil  : EvenList
    ECons : Nat -> OddList -> EvenList

data OddList : Type where
    OCons : Nat -> EvenList -> OddList

test : EvenList
test = ECons 1 ENil

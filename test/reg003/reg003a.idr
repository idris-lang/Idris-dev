
data EvenList : Set where
    ENil  : EvenList
    ECons : Nat -> OddList -> EvenList

data OddList : Set where
    OCons : Nat -> EvenList -> OddList                                                                                                                                                 

test : EvenList
test = ECons 1 ENil 

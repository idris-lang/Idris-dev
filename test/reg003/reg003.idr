
mutual
  namespace Even
    data EvenList : Set where
        Nil  : EvenList
        (::) : Nat -> OddList -> EvenList

  namespace Odd
    data OddList : Set where
        (::) : Nat -> EvenList -> OddList                                                                                                                                                 

test : EvenList
test = [1, 2, 3, 4, 5, 6]

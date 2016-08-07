
mutual
  namespace Even
    data EvenList : Type where
        Nil  : EvenList
        (::) : Nat -> OddList -> EvenList

  namespace Odd
    data OddList : Type where
        (::) : Nat -> EvenList -> OddList

test : EvenList
test = [1, 2, 3, 4, 5, 6]

f : Nat -> Nat 
f Z = Z     

g : Nat -> Nat 
g (f Z) = 1    

h : Int -> Int -> Int
h x x = x

data Parity : Nat -> Type where
     Even : Parity (n + n)
     Odd  : Parity (S (n + n))

foo : (n : Nat) -> Parity n -> Bool
foo (plus k k) Even = False
foo (S (plus k k)) Odd = True

data EqualLists : List () -> List () -> Type where
  EL : EqualLists l l

shouldWork : (l1,l2:List ()) -> EqualLists l1 l2 -> Bool
shouldWork [] [] EL = ?shouldWork_rhs_2
shouldWork (x :: xs) (x :: xs) EL = ?shouldWork_rhs_3

-- shouldWork [] [] EL = ?x_1
-- shouldWork (x :: xs) (x :: xs) EL = ?x_2

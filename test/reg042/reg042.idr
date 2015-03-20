-- This regtest tests for incorrect erasure from underapplied data constructors.

data T : Type where
    C : Nat -> Nat -> Nat -> T

data Q : Type where
    D : (Nat -> T) -> Q

-- The bug was here: (C 3 4) would compile to plain data,
-- not to a function that would expect another (albeit erased) argument.
f : Q
f = D (C 3 4)

proj : Nat -> Q -> Nat -> T
proj    Z  (D f) = f
proj (S n)    q  = proj n q

g : T -> Nat
g (C x y z) = x + y

-- Here, we'd apply the not-a-function to the erased argument 4,
-- which would make the program go wrong.
main : IO ()
main = printLn $ g (proj 3 f 4)

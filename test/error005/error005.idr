module error005

import Data.Fin

-- Test the Prelude's error rewrites for Fin

one : Fin 2
one = 1

two : Fin 2
two = 2

hahaha : (n : Nat) -> Fin n
hahaha n = 0

ok : (n : Nat) -> Fin (plus 2 n)
ok n = 1

notOk : (n : Nat) -> Fin (plus 2 n)
notOk n = 2

b0rken : Integer -> Fin 3
b0rken n = fromInteger n

x : Fin 4
x = the (Fin 4) 5


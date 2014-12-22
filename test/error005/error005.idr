module error005

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

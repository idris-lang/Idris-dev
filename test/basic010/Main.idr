module Main

qib : Nat -> Nat
qib       Z   = 1
qib    (S Z)  = 1
qib (S (S n)) = qib n * qib (S n)

f : (n : Nat) -> Exists (\k => qib n = k)
f n = witness (qib n) refl

main : IO ()
main = print "hello world"

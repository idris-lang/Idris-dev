module Main

qib : Nat -> Nat
qib       Z   = 1
qib    (S Z)  = 1
qib (S (S n)) = qib n * qib (S n)

f : (n : Nat) -> Exists (\k : Nat => qib n = k)
f n = evidence (qib n) refl

main : IO ()
main = print "hello world"

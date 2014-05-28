module Main

%default total

-- An expensive function.
qib : Nat -> Nat
qib       Z   = 2
qib    (S Z)  = 2
qib (S (S n)) = qib n * qib (S n)

-- An equality whose size reflects the size of numbers.
data equals : Nat -> Nat -> Type where
    eqZ : Z `equals` Z
    eqS : m `equals` n -> S m `equals` S n

eq_refl : {n : Nat} -> n `equals` n
eq_refl {n = Z}   = eqZ
eq_refl {n = S n} = eqS eq_refl

-- Here, the proof is very expensive to compute.
-- We add a recursive argument to prevent Idris from inlining it.
f : (r, n : Nat) -> Subset Nat (\k => qib n `equals` qib k)
f  Z    n = element n eq_refl
f (S r) n = f r n

-- Here, the witness is very expensive to compute.
-- We add a recursive argument to prevent Idris from inlining it.
g : (r, n : Nat) -> Exists (\k : Nat => k = qib n)
g  Z    n = evidence (qib n) refl
g (S r) n = g r n

nod : a -> IO ()
nod _ = putStrLn "*nod*"

main : IO ()
main = do
    nod $ getWitness (f 4 2)
    nod $ getProof   (g 4 2)

module Main

%default total

-- An expensive function.
qib : Nat -> Nat
qib       Z   = 1
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
-- We add a recursive argument to prevent Idris from inlining the function.
f : (r, n : Nat) -> Subset Nat (\k => qib n `equals` qib k)
f  Z    n = element n eq_refl
f (S r) n = f r n

-- A (contrived) relation, just to have something to show.
data represents : Nat -> Nat -> Type where
  axiom : (n : Nat) -> qib n `represents` n

-- Here, the witness is very expensive to compute.
-- We add a recursive argument to prevent Idris from inlining the function.
g : (r, n : Nat) -> Exists (\k : Nat => k `represents` n)
g  Z    n = evidence (qib n) (axiom n)
g (S r) n = g r n

fmt : qib n `represents` n -> String
fmt (axiom n) = "axiom " ++ show n

main : IO ()
main = do
    n <- map (const 10000) (putStrLn "*oink*")
    putStrLn . show $ getWitness (f 4 n)
    putStrLn . fmt  $ getProof   (g 4 n)

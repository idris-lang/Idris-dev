module Main

%default total

-- An expensive function.
qib : Nat -> Nat
qib       Z   = 1
qib    (S Z)  = 2
qib (S (S n)) = qib n * qib (S n)

-- An equality whose size reflects the size of numbers.
data Equals : Nat -> Nat -> Type where
    EqZ : Z `Equals` Z
    EqS : m `Equals` n -> S m `Equals` S n

eq_refl : {n : Nat} -> n `Equals` n
eq_refl {n = Z}   = EqZ
eq_refl {n = S n} = EqS eq_refl

-- Here, the proof is very expensive to compute.
-- We add a recursive argument to prevent Idris from inlining the function.
f : (r, n : Nat) -> Subset Nat (\k => qib n `Equals` qib k)
f  Z    n = Element n eq_refl
f (S r) n = f r n

-- A (contrived) relation, just to have something to show.
data Represents : Nat -> Nat -> Type where
  Axiom : (n : Nat) -> qib n `Represents` n

-- Here, the witness is very expensive to compute.
-- We add a recursive argument to prevent Idris from inlining the function.
g : (r, n : Nat) -> Exists (\k : Nat => k `Represents` n)
g  Z    n = Evidence (qib n) (Axiom n)
g (S r) n = g r n

fmt : qib n `Represents` n -> String
fmt (Axiom n) = "Axiom " ++ show n

main : IO ()
main = do
    n <- map (const (the Nat 10000)) (putStrLn "*oink*")
    putStrLn . show $ getWitness (f 4 n)
    putStrLn . fmt  $ getProof   (g 4 n)

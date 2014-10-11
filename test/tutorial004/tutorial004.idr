
fiveIsFive : 5 = 5
fiveIsFive = Refl

twoPlusTwo : 2 + 2 = 4
twoPlusTwo = Refl

total disjoint : (n : Nat) -> Z = S n -> Void
disjoint n p = replace {P = disjointTy} p ()
  where
    disjointTy : Nat -> Type
    disjointTy Z = ()
    disjointTy (S k) = Void

total acyclic : (n : Nat) -> n = S n -> Void
acyclic Z p = disjoint _ p
acyclic (S k) p = acyclic k (succInjective _ _ p)

empty1 : Void
empty1 = hd [] where
    hd : List a -> a
    hd (x :: xs) = x

empty2 : Void
empty2 = empty2

plusReduces : (n:Nat) -> plus Z n = n
plusReduces n = Refl

plusReducesZ : (n:Nat) -> n = plus n Z
plusReducesZ Z = Refl
plusReducesZ (S k) = cong (plusReducesZ k)

plusReducesS : (n:Nat) -> (m:Nat) -> S (plus n m) = plus n (S m)
plusReducesS Z m = Refl
plusReducesS (S k) m = cong (plusReducesS k m)

plusReducesZ' : (n:Nat) -> n = plus n Z
plusReducesZ' Z     = ?plusredZ_Z
plusReducesZ' (S k) = let ih = plusReducesZ' k in
                      ?plusredZ_S


---------- Proofs ----------

plusredZ_S = proof {
    intro;
    intro;
    rewrite ih;
    trivial;
}

plusredZ_Z = proof {
    compute;
    trivial;
}


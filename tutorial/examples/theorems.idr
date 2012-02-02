
fiveIsFive : 5 = 5
fiveIsFive = refl

twoPlusTwo : 2 + 2 = 4
twoPlusTwo = refl

total disjoint : (n : Nat) -> O = S n -> _|_
disjoint n p = replace {P = disjointTy} p ()
  where
    disjointTy : Nat -> Set
    disjointTy O = ()
    disjointTy (S k) = _|_

total acyclic : (n : Nat) -> n = S n -> _|_
acyclic O p = disjoint _ p
acyclic (S k) p = acyclic k (succInjective _ _ p)

empty1 : _|_
empty1 = hd [] where
    hd : List a -> a
    hd (x :: xs) = x

empty2 : _|_
empty2 = empty2

plusReduces : (n:Nat) -> plus O n = n
plusReduces n = refl

plusReducesO : (n:Nat) -> n = plus n O
plusReducesO O = refl
plusReducesO (S k) = cong (plusReducesO k)

plusReducesS : (n:Nat) -> (m:Nat) -> S (plus n m) = plus n (S m)
plusReducesS O m = refl
plusReducesS (S k) m = cong (plusReducesS k m)

plusReducesO' : (n:Nat) -> n = plus n O
plusReducesO' O     = ?plusredO_O
plusReducesO' (S k) = let ih = plusReducesO' k in
                      ?plusredO_S


---------- Proofs ----------

plusredO_S = proof {
    intro;
    intro;
    rewrite ih;
    trivial;
}

plusredO_O = proof {
    compute;
    trivial;
}


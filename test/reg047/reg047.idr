module test

data TTSigma : (A : Type) -> (B : A -> Type) -> Type where
    sigma : (A : Type) -> (B : A -> Type) -> (a : A) -> B a -> TTSigma A B

data Nat = zero | succ Nat

Id : (A : Type) -> A -> A -> Type
Id A = (=) {a0 = A} {b0 = A}

IdRefl : (A : Type) -> (a : A) -> Id A a a
IdRefl A a = Refl {a}

zzz : Id Nat zero zero
zzz = IdRefl Nat zero

eep : TTSigma Nat (\ a =>  Id Nat a zero)
eep = sigma Nat (\ a =>  Id Nat a zero) zero zzz

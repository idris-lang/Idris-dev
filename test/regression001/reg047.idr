module test

data TTSigma : (A : Type) -> (B : A -> Type) -> Type where
    Sigma : (A : Type) -> (B : A -> Type) -> (a : A) -> B a -> TTSigma A B

data Nat = Zero | Succ Nat

Id : (A : Type) -> A -> A -> Type
Id aTy = (=) {A = aTy} {B = aTy}

IdRefl : (A : Type) -> (a : A) -> Id A a a
IdRefl aTy a = Refl {x = a}

zzz : Id Nat Zero Zero
zzz = IdRefl Nat Zero

eep : TTSigma Nat (\ a =>  Id Nat a Zero)
eep = Sigma Nat (\ a =>  Id Nat a Zero) Zero zzz

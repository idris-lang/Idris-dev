module test

data TTSigma : (A : Type) -> (B : A -> Type) -> Type where
    sigma : (A : Type) -> (B : A -> Type) -> (a : A) -> B a -> TTSigma A B

data MNat = zero | succ MNat

Id : (A : Type) -> A -> A -> Type
Id = \A,x,y => x = y --  {a = A} {b = A}

Refl : (A : Type) -> (a : A) -> Id A a a
Refl A a = Refl {a}

zzzz : Id MNat zero zero
zzzz = Refl MNat zero

eep : TTSigma MNat (\ c =>  Id MNat c zero)
eep = (sigma MNat (\b => Id MNat b zero) zero zzzz)

eep2 : TTSigma MNat (\ c =>  Id MNat c zero)
eep2 = (sigma MNat (\b => Id MNat b zero) zero (Refl MNat zero))




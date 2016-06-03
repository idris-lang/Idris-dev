module test

data TTSigma : (A : Type) -> (B : A -> Type) -> Type where
    Sigma : (A : Type) -> (B : A -> Type) -> (a : A) -> B a -> TTSigma A B

data MNat = Zero | Succ MNat

Id : (A : Type) -> A -> A -> Type
Id = \A,x,y => x = y --  {a = A} {b = A}

IdRefl : (A : Type) -> (a : A) -> Id A a a
IdRefl A a = Refl {x = a}

zzzz : Id MNat Zero Zero
zzzz = IdRefl MNat Zero

eep : TTSigma MNat (\ c =>  Id MNat c Zero)
eep = (Sigma MNat (\b => Id MNat b Zero) Zero zzzz)

eep2 : TTSigma MNat (\ c =>  Id MNat c Zero)
eep2 = (Sigma MNat (\b => Id MNat b Zero) Zero (IdRefl MNat Zero))




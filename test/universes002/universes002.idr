module TypeInType

data MPair : (a : Type) -> (P : a -> Type) -> Type where
     MkMPair : .{P : a -> Type} -> (x : a) -> (pf : P x) -> MPair a P

data EQt : a -> b -> Type where
     REFL : EQt x x

msym : EQt x y -> EQt y x
msym REFL = REFL

mreplace : {a,x,y:_} -> {P : a -> Type} -> EQt x y -> P x -> P y
mreplace REFL p = p

data Tree : Type where
  Sup : (a : Type) -> (f : a -> Tree) -> Tree

A : Tree -> Type
A (Sup a _) = a

F : (t : Tree) -> A t -> Tree
F (Sup a f) = f

normal : Tree -> Type
normal t = (MPair (A t) (\y => EQt (F t y) (Sup (A t) (F t)))) -> Void

NT : Type
NT = MPair Tree (\t => normal t)

p : NT -> Tree
p (MkMPair x _) = x

R : Tree
R = Sup NT p

lemma : normal R
lemma (MkMPair (MkMPair y1 y2) z)
    = y2 
         (mreplace {P = (\ y3 => (MPair (A y3) 
                          (\y => EQt (F y3 y) (Sup (A y3) (F y3)))))} 
              (msym z) (MkMPair (MkMPair y1 y2) z))

total
russell : Void
russell = lemma (MkMPair (MkMPair R lemma) REFL) 

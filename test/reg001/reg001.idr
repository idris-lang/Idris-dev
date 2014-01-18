class Functor f => VerifiedFunctor (f : Type -> Type) where
   identity : (fa : f a) -> map id fa = fa

data Imp : Type where
   MkImp : {any : Type} -> any -> Imp

testVal : Imp
testVal = MkImp (apply id Z)

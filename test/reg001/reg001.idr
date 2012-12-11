apply : (a -> b) -> a -> b
apply f x = f x

class Functor f => VerifiedFunctor (f : Type -> Type) where 
   identity : (fa : f a) -> fmap id fa = fa 

data Imp : Type where 
   MkImp : {any : Type} -> any -> Imp

testVal : Imp
testVal = MkImp (apply id O)

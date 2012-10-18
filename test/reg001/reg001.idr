apply : (a -> b) -> a -> b
apply f x = f x

class Functor f => VerifiedFunctor (f : Set -> Set) where 
   identity : (fa : f a) -> fmap id fa = fa 

data Imp : Set where 
   MkImp : {any : Set} -> any -> Imp

testVal : Imp
testVal = MkImp (apply id O)

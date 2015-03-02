module FourFunctor

data FourFunctor y = Four y y y y

traverseFourFunctor : Applicative f -> 
      (x -> f b) -> FourFunctor x -> f (FourFunctor b)
traverseFourFunctor constr f (Four w x y z) 
   = pure Four <*> (f w) <*> (f x) <*> (f y) <*> (f z)


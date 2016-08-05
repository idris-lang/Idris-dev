module Foo

data Cheat : Type -> Type where
     CAny : a -> Cheat a
     CInt : Cheat Int

foo : Cheat a -> Int
foo (CAny Nothing) = 42 
foo (CAny (Just x)) = 43 
foo CInt = 0 

apply : (a -> a -> b) -> a -> a
apply (\x => \y => x) a = a
apply f a = a 


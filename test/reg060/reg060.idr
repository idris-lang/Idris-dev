
class MyFunctor (f : Type -> Type) where
  mymap : (m : a -> b) -> f a -> f b

data Foo x y = Bar y

instance MyFunctor (Foo m) where
  mymap m x = ?wibble

instance [foo] Functor m => MyFunctor m where
  mymap m x = map m x


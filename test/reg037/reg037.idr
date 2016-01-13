
--- Parser regression for (=) as a function name (fnName)

interface Foo (t : a -> b -> Type) where
  foo : (x : _) -> (y : _) -> t x y -> t x y

implementation Foo ((=) {A=a} {B=b}) where
  foo x y prf = prf


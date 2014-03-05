
--- Parser regression for (=) as a function name (fnName)

class Foo (t : (A : Type) -> (B : Type) -> A -> B -> Type) where
  foo : (A : Type) -> (B : Type) -> (x : A) -> (y : B) -> t A B x y -> t A B x y

instance Foo (=) where
  foo A B x y prf = prf


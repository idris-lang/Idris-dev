module Foo

f : Type -> Type
f x = f x

bad : f Nat
bad = Z


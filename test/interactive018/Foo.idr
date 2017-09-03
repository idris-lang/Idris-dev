module Foo

foo_private : Nat -> Nat
foo_private n = n

export
foo_visible : Nat -> Nat
foo_visible n = n

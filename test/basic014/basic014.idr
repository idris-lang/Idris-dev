-- Test pattern unification

import Data.Vect

comp : {A : Type} -> {B : (a : A) -> Type} ->
       {C : (a : A) -> (b : B a) -> Type} ->
       (f : {a : A} -> (b : B a) -> C a b) ->
       (g : (a : A) -> B a) ->
       (a : A) -> C a (g a)
comp f g a = f (g a)

add2 : Nat -> Nat
add2 = comp S S

data Foo = MkFoo
data Bar = MkBar

foo : Foo -> Bar

bar : Bar -> Nat

baz : Foo -> Nat
baz = (comp bar foo)

comp0 : (B : Nat -> Type) -> ((n : Nat) -> B n) -> Int
comp0 _ _ = 0

test00 : Int
test00 = comp0 _ S

comp2 : (B : Nat -> Type) ->
        ((n : Nat) -> (y : B n) -> Int) -> Int
comp2 _ _ = 0

test20 : Int
test20 = comp2 _ dummy
  where
    dummy : (n : Nat) -> Vect n Int -> Int
    dummy _ _ = 0

test03 : Int
test03 = comp0 _ dummy where
    dummy : (n : Nat) -> Int -> Int
    dummy _ = \x => x

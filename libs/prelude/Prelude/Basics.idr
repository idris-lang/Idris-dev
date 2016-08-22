module Prelude.Basics

import Builtins

%access public export

Not : Type -> Type
Not a = a -> Void

||| Identity function.
id : a -> a
id x = x

||| Manually assign a type to an expression.
||| @ a the type to assign
||| @ value the element to get the type
the : (a : Type) -> (value : a) -> a
the _ = id

||| Constant function. Ignores its second argument.
const : a -> b -> a
const x = \value => x

||| Return the first element of a pair.
fst : (a, b) -> a
fst (x, y) = x

||| Return the second element of a pair.
snd : (a, b) -> b
snd (x, y) = y

infixl 9 .

||| Function composition
(.) : (b -> c) -> (a -> b) -> a -> c
(.) f g = \x => f (g x)

||| Takes in the first two arguments in reverse order.
||| @ f the function to flip
flip : (f : a -> b -> c) -> b -> a -> c
flip f x y = f y x

||| Function application.
apply : (a -> b) -> a -> b
apply f a = f a

||| Equality is a congruence.
cong : {f : t -> u} -> (a = b) -> f a = f b
cong Refl = Refl

||| Decidability. A decidable property either holds or is a contradiction.
data Dec : Type -> Type where

  ||| The case where the property holds
  ||| @ prf the proof
  Yes : (prf : prop) -> Dec prop

  ||| The case where the property holding would be a contradiction
  ||| @ contra a demonstration that prop would be a contradiction
  No  : (contra : prop -> Void) -> Dec prop


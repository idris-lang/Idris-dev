module Prelude.Basics

Not : Type -> Type
Not a = a -> _|_

||| Identity function.
id : a -> a
id x = x

||| Manually assign a type to an expression.
||| @ a the type to assign
||| @ x the element to get the type
the : (a : Type) -> (x : a) -> a
the _ = id

||| Constant function. Ignores its second argument.
const : a -> b -> a
const x = \v => x

||| Return the first element of a pair.
fst : (s, t) -> s
fst (x, y) = x

||| Return the second element of a pair.
snd : (a, b) -> b
snd (x, y) = y

infixl 9 .

||| Function composition
(.) : (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

||| Takes in the first two arguments in reverse order.
||| @ f the function to flip
flip : (f : a -> b -> c) -> b -> a -> c
flip f x y = f y x

||| Function application.
apply : (a -> b) -> a -> b
apply f a = f a

||| Equality is a congruence.
cong : {f : t -> u} -> (a = b) -> f a = f b
cong refl = refl

||| Decidability. A decidable property either holds or is a contradiction.
data Dec : Type -> Type where

  ||| The case where the property holds
  ||| @ prf the proof
  Yes : {A : Type} -> (prf : A) -> Dec A

  ||| The case where the property holding would be a contradiction
  ||| @ contra a demonstration that A would be a contradiction
  No  : {A : Type} -> (contra : A -> _|_) -> Dec A


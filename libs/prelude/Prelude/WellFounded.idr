||| Well-founded recursion.
|||
||| This is to let us implement some functions that don't have trivial
||| recursion patterns over datatypes, but instead are using some
||| other metric of size.
module Prelude.WellFounded

import Builtins

import Prelude.Nat
import Prelude.List
import Prelude.Uninhabited

%default total
%access public export

||| Accessibility: some element `x` is accessible if all `y` such that
||| `rel y x` are themselves accessible.
|||
||| @ a the type of elements
||| @ rel a relation on a
||| @ x the acessible element
data Accessible : (rel : a -> a -> Type) -> (x : a) -> Type where
  ||| Accessibility
  |||
  ||| @ x the accessible element
  ||| @ rec a demonstration that all smaller elements are also accessible
  Access : (rec : (y : a) -> rel y x -> Accessible rel y) ->
           Accessible rel x

||| A relation `rel` on `a` is well-founded if all elements of `a` are
||| acessible.
|||
||| @ rel the well-founded relation
interface WellFounded (rel : a -> a -> Type) where
  wellFounded : (x : _) -> Accessible rel x


||| A recursor over accessibility.
|||
||| This allows us to recurse over the subset of some type that is
||| accessible according to some relation.
|||
||| @ rel the well-founded relation
||| @ step how to take steps on reducing arguments
||| @ z the starting point
accRec : {rel : a -> a -> Type} ->
         (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
         (z : a) -> Accessible rel z -> b
accRec step z (Access f) =
  step z $ \y, lt => accRec step y (f y lt)

||| An induction principle for accessibility.
|||
||| This allows us to recurse over the subset of some type that is
||| accessible according to some relation, producing a dependent type
||| as a result.
|||
||| @ rel the well-founded relation
||| @ step how to take steps on reducing arguments
||| @ z the starting point
accInd : {rel : a -> a -> Type} -> {P : a -> Type} ->
         (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
         (z : a) -> Accessible rel z -> P z
accInd {P=p} step z (Access f) =
  step z $ \y, lt => accInd {P=p} step y (f y lt)


||| Use well-foundedness of a relation to write terminating operations.
|||
||| @ rel a well-founded relation
wfRec : WellFounded rel =>
        (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
        a -> b
wfRec {rel} step x = accRec step x (wellFounded {rel} x)


||| Use well-foundedness of a relation to write proofs
|||
||| @ rel a well-founded relation
||| @ P the motive for the induction
||| @ step the induction step: take an element and its accessibility,
|||        and give back a demonstration of P for that element,
|||        potentially using accessibility
wfInd : WellFounded rel => {P : a -> Type} ->
        (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
        (x : a) -> P x
wfInd {rel} step x = accInd step x (wellFounded {rel} x)

||| Interface of types with sized values.
||| The size is used for proofs of termination via accessibility.
|||
||| @ a the type whose elements can be mapped to Nat
interface Sized a where
  size : a -> Nat

Smaller : Sized a => a -> a -> Type
Smaller x y = size x `LT` size y

SizeAccessible : Sized a => a -> Type
SizeAccessible = Accessible Smaller

||| Proof of well-foundedness of `Smaller`.
||| Constructs accessibility for any given element of `a`, provided `Sized a`.
sizeAccessible : Sized a => (x : a) -> SizeAccessible x
sizeAccessible x = Access (acc $ size x)
  where
    acc : (sizeX : Nat) -> (y : a) -> (size y `LT` sizeX) -> SizeAccessible y
    acc (S x') y (LTESucc yLEx')
        = Access (\z, zLTy => acc x' z (lteTransitive zLTy yLEx'))

||| Strong induction principle for sized types.
sizeInd : Sized a
  => {P : a -> Type}
  -> (step : (x : a) -> ((y : a) -> Smaller y x -> P y) -> P x)
  -> (z : a)
  -> P z
sizeInd step z = accInd step z (sizeAccessible z)

||| Strong recursion principle for sized types.
sizeRec : Sized a
  => (step : (x : a) -> ((y : a) -> Smaller y x -> b) -> b)
  -> (z : a)
  -> b
sizeRec step z = accRec step z (sizeAccessible z)


implementation Sized Nat where
  size = \x => x

implementation Sized (List a) where
  size = length

implementation (Sized a, Sized b) => Sized (Pair a b) where
  size (x,y) = Nat.plus (size x) (size y)

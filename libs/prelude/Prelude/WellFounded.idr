||| Well-founded recursion.
|||
||| This is to let us implement some functions that don't have trivial
||| recursion patterns over datatypes, but instead are using some
||| other metric of size.
module Prelude.WellFounded

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
accInd {P} step z (Access f) =
  step z $ \y, lt => accInd {P} step y (f y lt)


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

-- Some basic useful relations

||| LT is a well-founded relation on numbers
ltAccessible : (n : Nat) -> Accessible LT n
ltAccessible n = Access (\v, prf => ltAccessible' {n'=v} n prf)
  where
    ltAccessible' : (m : Nat) -> LT n' m -> Accessible LT n'
    ltAccessible' Z x = absurd x 
    ltAccessible' (S k) (LTESucc x) 
        = Access (\val, p => ltAccessible' k (lteTransitive p x))

-- First list is smaller than the second
smaller : List a -> List a -> Type
smaller xs ys = LT (length xs) (length ys)

||| `smaller` is a well-founded relation on lists
smallerAcc : (xs : List a) -> Accessible WellFounded.smaller xs
smallerAcc xs = Access (\v, prf => smallerAcc' {xs'=v} xs prf)
  where
    smallerAcc' : (ys : List a) -> smaller xs' ys -> Accessible smaller xs'
    smallerAcc' [] x = absurd x
    smallerAcc' (y :: ys) (LTESucc x) 
       = Access (\val, p => smallerAcc' ys (lteTransitive p x))



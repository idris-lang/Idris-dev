||| Definition and general theorems about equivalence
||| relations, including examples.
module Relations.Equivalence
import Basics
import Orders

%default total
%access public

||| An equivalence relation is a reflexive, transitive, and symmetric
||| relation.
data Equivalence : Rel a -> Type where
  MkEquivalence : (rfl : Reflexive rel) -> (trns : Transitive rel) ->
                  (symm : Symmetric rel) -> Equivalence rel

||| An equivalence relation is a preorder.
equivalenceIsPreorder : Equivalence rel -> Preorder rel
equivalenceIsPreorder (MkEquivalence rfl trns symm) =
  MkPreorder rfl trns

||| The `(=)` relation on any given type is an equivalence.
equalityIsEquivalence : {a:Type} -> Equivalence ((=) {A=a} {B=a})
equalityIsEquivalence {a} = MkEquivalence (\x => Refl) (\x,y,z => trans) (\x,y=>sym)

||| Equivalence of relations is an equivalence relation.
equivalentIsEquivalence : Equivalence Equivalent
equivalentIsEquivalence = MkEquivalence rfl trns symm
  where
    rfl : (rel : a -> a -> Type) -> Equivalent rel rel
    rfl rel = MkEquivalent (\x,y,rel=>rel) (\x,y,rel=>rel)
    symm : (rel1 : a -> a -> Type) ->
           (rel2 : a -> a -> Type) -> Equivalent rel1 rel2 -> Equivalent rel2 rel1
    symm rel1 rel2 (MkEquivalent f g) = MkEquivalent g f
    trns : (rel1 : a -> a -> Type) ->
           (rel2 : a -> a -> Type) ->
           (rel3 : a -> a -> Type) ->
           Equivalent rel1 rel2 -> Equivalent rel2 rel3 -> Equivalent rel1 rel3
    trns rel1 rel2 rel3 (MkEquivalent f g) (MkEquivalent h i) =
      MkEquivalent (\x,y,r => h x y (f x y r))
                   (\x,y,r => g x y (i x y r))

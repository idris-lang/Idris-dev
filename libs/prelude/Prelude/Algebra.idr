module Prelude.Algebra

import Builtins

infixl 6 <+>

%access public export

--------------------------------------------------------------------------------
-- A modest interface hierarchy
--------------------------------------------------------------------------------

||| Sets equipped with a single binary operation that is associative.  Must
||| satisfy the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
interface Semigroup ty where
  (<+>) : ty -> ty -> ty

  semigroupOpIsAssociative : (l, c, r : ty) ->
    l <+> (c <+> r) = (l <+> c) <+> r

||| Sets equipped with a single binary operation that is associative, along with
||| a neutral element for that binary operation.  Must satisfy the following
||| laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
interface Semigroup ty => Monoid ty where
  neutral : ty

  monoidNeutralIsNeutralL : (l : ty) -> l <+> Algebra.neutral = l
  monoidNeutralIsNeutralR : (r : ty) -> Algebra.neutral <+> r = r

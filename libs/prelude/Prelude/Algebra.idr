module Prelude.Algebra

import Builtins

-- XXX: change?
infixl 6 <->
infixl 6 <+>
infixl 6 <*>

%access public

--------------------------------------------------------------------------------
-- A modest class hierarchy
--------------------------------------------------------------------------------

||| Sets equipped with a single binary operation that is associative.  Must
||| satisfy the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
class Semigroup a where
  (<+>) : a -> a -> a

class Semigroup a => VerifiedSemigroup a where
  total semigroupOpIsAssociative : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r

||| Sets equipped with a single binary operation that is associative, along with
||| a neutral element for that binary operation.  Must satisfy the following
||| laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
class Semigroup a => Monoid a where
  neutral : a

class (VerifiedSemigroup a, Monoid a) => VerifiedMonoid a where
  total monoidNeutralIsNeutralL : (l : a) -> l <+> neutral = l
  total monoidNeutralIsNeutralR : (r : a) -> neutral <+> r = r

module Prelude.Algebra

import Builtins

-- XXX: change?
infixl 6 <->
infixl 6 <+>
infixl 6 <.>

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

||| Sets equipped with a single binary operation that is associative, along with
||| a neutral element for that binary operation and inverses for all elements.
||| Must satisfy the following laws:
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
||| + Inverse for `<+>`:
|||     forall a,     a <+> inverse a == neutral
|||     forall a,     inverse a <+> a == neutral
class Monoid a => Group a where
  inverse : a -> a

class (VerifiedMonoid a, Group a) => VerifiedGroup a where
  total groupInverseIsInverseL : (l : a) -> l <+> inverse l = neutral
  total groupInverseIsInverseR : (r : a) -> inverse r <+> r = neutral

(<->) : Group a => a -> a -> a
(<->) left right = left <+> (inverse right)

||| Sets equipped with a single binary operation that is associative and
||| commutative, along with a neutral element for that binary operation and
||| inverses for all elements. Must satisfy the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Commutativity of `<+>`:
|||     forall a b,   a <+> b         == b <+> a
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
||| + Inverse for `<+>`:
|||     forall a,     a <+> inverse a == neutral
|||     forall a,     inverse a <+> a == neutral
class Group a => AbelianGroup a where { }

class (VerifiedGroup a, AbelianGroup a) => VerifiedAbelianGroup a where
  total abelianGroupOpIsCommutative : (l, r : a) -> l <+> r = r <+> l

||| Sets equipped with two binary operations, one associative and commutative
||| supplied with a neutral element, and the other associative, with
||| distributivity laws relating the two operations.  Must satisfy the following
||| laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Commutativity of `<+>`:
|||     forall a b,   a <+> b         == b <+> a
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
||| + Inverse for `<+>`:
|||     forall a,     a <+> inverse a == neutral
|||     forall a,     inverse a <+> a == neutral
||| + Associativity of `<.>`:
|||     forall a b c, a <.> (b <.> c) == (a <.> b) <.> c
||| + Distributivity of `<.>` and `<->`:
|||     forall a b c, a <.> (b <+> c) == (a <.> b) <+> (a <.> c)
|||     forall a b c, (a <+> b) <.> c == (a <.> c) <+> (b <.> c)
class AbelianGroup a => Ring a where
  (<.>) : a -> a -> a

class (VerifiedAbelianGroup a, Ring a) => VerifiedRing a where
  total ringOpIsAssociative   : (l, c, r : a) -> l <.> (c <.> r) = (l <.> c) <.> r
  total ringOpIsDistributiveL : (l, c, r : a) -> l <.> (c <+> r) = (l <.> c) <+> (l <.> r)
  total ringOpIsDistributiveR : (l, c, r : a) -> (l <+> c) <.> r = (l <.> r) <+> (c <.> r)

||| Sets equipped with two binary operations, one associative and commutative
||| supplied with a neutral element, and the other associative supplied with a
||| neutral element, with distributivity laws relating the two operations.  Must
||| satisfy the following laws:
|||
||| +  Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Commutativity of `<+>`:
|||     forall a b,   a <+> b         == b <+> a
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
||| + Inverse for `<+>`:
|||     forall a,     a <+> inverse a == neutral
|||     forall a,     inverse a <+> a == neutral
||| + Associativity of `<.>`:
|||     forall a b c, a <.> (b <.> c) == (a <.> b) <.> c
||| + Neutral for `<.>`:
|||     forall a,     a <.> unity     == a
|||     forall a,     unity <.> a     == a
||| + Distributivity of `<.>` and `<->`:
|||     forall a b c, a <.> (b <+> c) == (a <.> b) <+> (a <.> c)
|||     forall a b c, (a <+> b) <.> c == (a <.> c) <+> (b <.> c)
class Ring a => RingWithUnity a where
  unity : a

class (VerifiedRing a, RingWithUnity a) => VerifiedRingWithUnity a where
  total ringWithUnityIsUnityL : (l : a) -> l <.> unity = l
  total ringWithUnityIsUnityR : (r : a) -> unity <.> r = r

||| Sets equipped with two binary operations – both associative, commutative and
||| possessing a neutral element – and distributivity laws relating the two 
||| operations. All elements except the additive identity must have a 
||| multiplicative inverse. Must satisfy the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Commutativity of `<+>`:
|||     forall a b,   a <+> b         == b <+> a
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
||| + Inverse for `<+>`:
|||     forall a,     a <+> inverse a == neutral
|||     forall a,     inverse a <+> a == neutral
||| + Associativity of `<.>`:
|||     forall a b c, a <.> (b <.> c) == (a <.> b) <.> c
||| + Unity for `<.>`:
|||     forall a,     a <.> unity     == a
|||     forall a,     unity <.> a     == a
||| + InverseM of `<.>`, except for neutral
|||     forall a /= neutral,  a <.> inverseM a == unity
|||     forall a /= neutral,  inverseM a <.> a == unity
||| + Distributivity of `<.>` and `<->`:
|||     forall a b c, a <.> (b <+> c) == (a <.> b) <+> (a <.> c)
|||     forall a b c, (a <+> b) <.> c == (a <.> c) <+> (b <.> c)
class RingWithUnity a => Field a where
  inverseM : a -> a

class (VerifiedRing a, Field a) => VerifiedField a where
  total fieldInverseIsInverseL : (l : a) -> l <.> inverseM l = unity
  total fieldInverseIsInverseR : (r : a) -> inverseM r <.> r = unity


-- XXX todo:
--   Structures where "abs" make sense.
--   Euclidean domains, etc.
--   Where to put fromInteger and fromRational?

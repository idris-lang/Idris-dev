module Control.Algebra

infixl 6 <->
infixl 6 <.>


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

||| Sets equipped with two binary operations, both associative and commutative
||| supplied with a neutral element, with
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
||| + Unity for `<.>`:
|||     forall a,     a <.> unity     == a
|||     forall a,     unity <.> a     == a
||| + InverseM of `<.>`:
|||     forall a,     a <.> inverseM a == unity
|||     forall a,     inverseM a <.> a == unity
||| + Distributivity of `<.>` and `<->`:
|||     forall a b c, a <.> (b <+> c) == (a <.> b) <+> (a <.> c)
|||     forall a b c, (a <+> b) <.> c == (a <.> c) <+> (b <.> c)
class RingWithUnity a => Field a where
  inverseM : a -> a


-- XXX todo:
--   Structures where "abs" make sense.
--   Euclidean domains, etc.
--   Where to put fromInteger and fromRational?

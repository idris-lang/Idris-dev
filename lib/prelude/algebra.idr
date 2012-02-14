module prelude.algebra

import builtins

-- XXX: change?
infixl 6 <->
infixl 6 <+>
infixl 6 <*>

%access public

-- Sets equipped with a single binary operation that is associative.  Must
-- satisfy the following laws:
--   Associativity of <+>:
--     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
class Semigroup a where
  (<+>) : a -> a -> a

-- Sets equipped with a single binary operation that is associative, along with
-- a neutral element for that binary operation.  Must satisfy the following
-- laws:
--   Associativity of <+>:
--     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
--   Neutral for <+>:
--     forall a,     a <+> neutral   == a
--     forall a,     neutral <+> a   == a
class Semigroup a => Monoid a where
  neutral : a

-- Sets equipped with a single binary operation that is associative, along with
-- a neutral element for that binary operation and inverses for all elements.
-- Must satisfy the following laws:
--   Associativity of <+>:
--     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
--   Neutral for <+>:
--     forall a,     a <+> neutral   == a
--     forall a,     neutral <+> a   == a
--   Inverse for <+>:
--     forall a,     a <+> inverse a == neutral
--     forall a,     inverse a <+> a == neutral
class Monoid a => Group a where
  inverse : a -> a

(<->) : Group a => a -> a -> a
(<->) left right = left <+> (inverse right)

-- Sets equipped with a single binary operation that is associative and
-- commutative, along with a neutral element for that binary operation and
-- inverses for all elements. Must satisfy the following laws:
--   Associativity of <+>:
--     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
--   Commutativity of <+>:
--     forall a b,   a <+> b         == b <+> a
--   Neutral for <+>:
--     forall a,     a <+> neutral   == a
--     forall a,     neutral <+> a   == a
--   Inverse for <+>:
--     forall a,     a <+> inverse a == neutral
--     forall a,     inverse a <+> a == neutral
class Group a => AbelianGroup a where { }

-- Sets equipped with two binary operations, one associative and commutative
-- supplied with a neutral element, and the other associative, with
-- distributivity laws relating the two operations.  Must satisfy the following
-- laws:
--   Associativity of <+>:
--     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
--   Commutativity of <+>:
--     forall a b,   a <+> b         == b <+> a
--   Neutral for <+>:
--     forall a,     a <+> neutral   == a
--     forall a,     neutral <+> a   == a
--   Inverse for <+>:
--     forall a,     a <+> inverse a == neutral
--     forall a,     inverse a <+> a == neutral
--   Associativity of <*>:
--     forall a b c, a <*> (b <*> c) == (a <*> b) <*> c
--   Distributivity of <*> and <->:
--     forall a b c, a <*> (b <+> c) == (a <*> b) <+> (a <*> c)
--     forall a b c, (a <+> b) <*> c == (a <*> c) <+> (b <*> c)
class AbelianGroup a => Ring a where
  (<*>) : a -> a -> a

-- Sets equipped with two binary operations, one associative and commutative
-- supplied with a neutral element, and the other associative supplied with a
-- neutral element, with distributivity laws relating the two operations.  Must
-- satisfy the following laws:
--   Associativity of <+>:
--     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
--   Commutativity of <+>:
--     forall a b,   a <+> b         == b <+> a
--   Neutral for <+>:
--     forall a,     a <+> neutral   == a
--     forall a,     neutral <+> a   == a
--   Inverse for <+>:
--     forall a,     a <+> inverse a == neutral
--     forall a,     inverse a <+> a == neutral
--   Associativity of <*>:
--     forall a b c, a <*> (b <*> c) == (a <*> b) <*> c
--   Neutral for <*>:
--     forall a,     a <*> unity     == a
--     forall a,     unity <*> a     == a
--   Distributivity of <*> and <->:
--     forall a b c, a <*> (b <+> c) == (a <*> b) <+> (a <*> c)
--     forall a b c, (a <+> b) <*> c == (a <*> c) <+> (b <*> c)
class Ring a => RingWithUnity a where
  unity : a

-- Sets equipped with a binary operation that is commutative, associative and
-- idempotent.  Must satisfy the following laws:
--   Associativity of join:
--     forall a b c, join a (join b c) == join (join a b) c
--   Commutativity of join:
--     forall a b,   join a b          == join b a
--   Idempotency of join:
--     forall a,     join a a          == a
--  Join semilattices capture the notion of sets with a "least upper bound".
class JoinSemilattice a where
  join : a -> a -> a

-- Sets equipped with a binary operation that is commutative, associative and
-- idempotent.  Must satisfy the following laws:
--   Associativity of meet:
--     forall a b c, meet a (meet b c) == meet (meet a b) c
--   Commutativity of meet:
--     forall a b,   meet a b          == meet b a
--   Idempotency of meet:
--     forall a,     meet a a          == a
--  Meet semilattices capture the notion of sets with a "greatest lower bound".
class MeetSemilattice a where
  meet : a -> a -> a

-- Sets equipped with a binary operation that is commutative, associative and
-- idempotent and supplied with a neutral element.  Must satisfy the following
-- laws:
--   Associativity of join:
--     forall a b c, join a (join b c) == join (join a b) c
--   Commutativity of join:
--     forall a b,   join a b          == join b a
--   Idempotency of join:
--     forall a,     join a a          == a
--   Neutral for join:
--     forall a,     join a bottom     == bottom
--  Join semilattices capture the notion of sets with a "least upper bound"
--  equipped with a "bottom" element.
class JoinSemilattice a => BoundedJoinSemilattice a where
  bottom  : a

-- Sets equipped with a binary operation that is commutative, associative and
-- idempotent and supplied with a neutral element.  Must satisfy the following
-- laws:
--   Associativity of meet:
--     forall a b c, meet a (meet b c) == meet (meet a b) c
--   Commutativity of meet:
--     forall a b,   meet a b          == meet b a
--   Idempotency of meet:
--     forall a,     meet a a          == a
--   Neutral for meet:
--     forall a,     meet a top        == top
--  Meet semilattices capture the notion of sets with a "greatest lower bound"
--  equipped with a "top" element.
class MeetSemilattice a => BoundedMeetSemilattice a where
  top : a

-- Sets equipped with two binary operations that are both commutative,
-- associative and idempotent, along with absorbtion laws for relating the two
-- binary operations.  Must satisfy the following:
--   Associativity of meet and join:
--     forall a b c, meet a (meet b c) == meet (meet a b) c
--     forall a b c, join a (join b c) == join (join a b) c
--   Commutativity of meet and join:
--     forall a b,   meet a b          == meet b a
--     forall a b,   join a b          == join b a
--   Idempotency of meet and join:
--     forall a,     meet a a          == a
--     forall a,     join a a          == a
--   Absorbtion laws for meet and join:
--     forall a b,   meet a (join a b) == a
--     forall a b,   join a (meet a b) == a
class (JoinSemilattice a, MeetSemilattice a) => Lattice a where { }

-- Sets equipped with two binary operations that are both commutative,
-- associative and idempotent and supplied with neutral elements, along with
-- absorbtion laws for relating the two binary operations.  Must satisfy the
-- following:
--   Associativity of meet and join:
--     forall a b c, meet a (meet b c) == meet (meet a b) c
--     forall a b c, join a (join b c) == join (join a b) c
--   Commutativity of meet and join:
--     forall a b,   meet a b          == meet b a
--     forall a b,   join a b          == join b a
--   Idempotency of meet and join:
--     forall a,     meet a a          == a
--     forall a,     join a a          == a
--   Absorbtion laws for meet and join:
--     forall a b,   meet a (join a b) == a
--     forall a b,   join a (meet a b) == a
--   Neutral for meet and join:
--     forall a,     meet a top        == top
--     forall a,     join a bottom     == bottom
class (BoundedJoinSemilattice a, BoundedMeetSemilattice a) => BoundedLattice a where { }
  
-- XXX todo:
--   Fields and vector spaces.
--   Structures where "abs" make sense.
--   Euclidean domains, etc.
--   Where to put fromInteger and fromRational?

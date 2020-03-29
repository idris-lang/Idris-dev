module Control.Algebra.Lattice

import Control.Algebra
import Data.Bool.Extra

%access public export

||| Sets equipped with a binary operation that is commutative, associative and
||| idempotent.  Must satisfy the following laws:
|||
||| + Associativity of join:
|||     forall a b c, join a (join b c) == join (join a b) c
||| + Commutativity of join:
|||     forall a b,   join a b          == join b a
||| + Idempotency of join:
|||     forall a,     join a a          == a
|||
||| Join semilattices capture the notion of sets with a "least upper bound".
interface JoinSemilattice a where
  join : a -> a -> a

  joinSemilatticeJoinIsAssociative : (l, c, r : a) -> join l (join c r) = join (join l c) r
  joinSemilatticeJoinIsCommutative : (l, r : a)    -> join l r = join r l
  joinSemilatticeJoinIsIdempotent  : (e : a)       -> join e e = e

||| Sets equipped with a binary operation that is commutative, associative and
||| idempotent.  Must satisfy the following laws:
|||
||| + Associativity of meet:
|||     forall a b c, meet a (meet b c) == meet (meet a b) c
||| + Commutativity of meet:
|||     forall a b,   meet a b          == meet b a
||| + Idempotency of meet:
|||     forall a,     meet a a          == a
|||
||| Meet semilattices capture the notion of sets with a "greatest lower bound".
interface MeetSemilattice a where
  meet : a -> a -> a

  meetSemilatticeMeetIsAssociative : (l, c, r : a) -> meet l (meet c r) = meet (meet l c) r
  meetSemilatticeMeetIsCommutative : (l, r : a)    -> meet l r = meet r l
  meetSemilatticeMeetIsIdempotent  : (e : a)       -> meet e e = e

||| Sets equipped with a binary operation that is commutative, associative and
||| idempotent and supplied with a unitary element.  Must satisfy the following
||| laws:
|||
||| + Associativity of join:
|||     forall a b c, join a (join b c) == join (join a b) c
||| + Commutativity of join:
|||     forall a b,   join a b          == join b a
||| + Idempotency of join:
|||     forall a,     join a a          == a
||| + Bottom (Unitary Element):
|||     forall a,     join a bottom     == a
|||
|||  Join semilattices capture the notion of sets with a "least upper bound"
|||  equipped with a "bottom" element.
interface JoinSemilattice a => BoundedJoinSemilattice a where
  bottom  : a

  joinBottomIsIdentity : (x : a) -> join x Lattice.bottom = x

||| Sets equipped with a binary operation that is commutative, associative and
||| idempotent and supplied with a unitary element.  Must satisfy the following
||| laws:
|||
||| + Associativity of meet:
|||     forall a b c, meet a (meet b c) == meet (meet a b) c
||| + Commutativity of meet:
|||     forall a b,   meet a b          == meet b a
||| + Idempotency of meet:
|||     forall a,     meet a a          == a
||| +  Top (Unitary Element):
|||     forall a,     meet a top        == a
|||
||| Meet semilattices capture the notion of sets with a "greatest lower bound"
||| equipped with a "top" element.
interface MeetSemilattice a => BoundedMeetSemilattice a where
  top : a

  meetTopIsIdentity : (x : a) -> meet x Lattice.top = x

||| Sets equipped with two binary operations that are both commutative,
||| associative and idempotent, along with absorbtion laws for relating the two
||| binary operations.  Must satisfy the following:
|||
||| + Associativity of meet and join:
|||     forall a b c, meet a (meet b c) == meet (meet a b) c
|||     forall a b c, join a (join b c) == join (join a b) c
||| + Commutativity of meet and join:
|||     forall a b,   meet a b          == meet b a
|||     forall a b,   join a b          == join b a
||| + Idempotency of meet and join:
|||     forall a,     meet a a          == a
|||     forall a,     join a a          == a
||| + Absorbtion laws for meet and join:
|||     forall a b,   meet a (join a b) == a
|||     forall a b,   join a (meet a b) == a
interface (JoinSemilattice a, MeetSemilattice a) => Lattice a where { }

||| Sets equipped with two binary operations that are both commutative,
||| associative and idempotent and supplied with neutral elements, along with
||| absorbtion laws for relating the two binary operations.  Must satisfy the
||| following:
|||
||| + Associativity of meet and join:
|||     forall a b c, meet a (meet b c) == meet (meet a b) c
|||     forall a b c, join a (join b c) == join (join a b) c
||| +  Commutativity of meet and join:
|||     forall a b,   meet a b          == meet b a
|||     forall a b,   join a b          == join b a
||| + Idempotency of meet and join:
|||     forall a,     meet a a          == a
|||     forall a,     join a a          == a
||| + Absorbtion laws for meet and join:
|||     forall a b,   meet a (join a b) == a
|||     forall a b,   join a (meet a b) == a
||| + Neutral for meet and join:
|||     forall a,     meet a top        == top
|||     forall a,     join a bottom     == bottom
interface (BoundedJoinSemilattice a, BoundedMeetSemilattice a) => BoundedLattice a where { }

-- Implementations ---------------------

-- Nat

JoinSemilattice Nat where
  join = maximum
  joinSemilatticeJoinIsAssociative = maximumAssociative
  joinSemilatticeJoinIsCommutative = maximumCommutative
  joinSemilatticeJoinIsIdempotent  = maximumIdempotent

MeetSemilattice Nat where
  meet = minimum
  meetSemilatticeMeetIsAssociative = minimumAssociative
  meetSemilatticeMeetIsCommutative = minimumCommutative
  meetSemilatticeMeetIsIdempotent  = minimumIdempotent

BoundedJoinSemilattice Nat where
  bottom = Z
  joinBottomIsIdentity = maximumZeroNLeft

Lattice Nat where { }

-- Bool

JoinSemilattice Bool where
  join a b = a || b
  joinSemilatticeJoinIsAssociative = orAssociative
  joinSemilatticeJoinIsCommutative = orCommutative
  joinSemilatticeJoinIsIdempotent = orSameNeutral

MeetSemilattice Bool where
  meet a b = a && b
  meetSemilatticeMeetIsAssociative = andAssociative
  meetSemilatticeMeetIsCommutative = andCommutative
  meetSemilatticeMeetIsIdempotent = andSameNeutral

BoundedJoinSemilattice Bool where
  bottom = False
  joinBottomIsIdentity = orFalseNeutral

BoundedMeetSemilattice Bool where
  top = True
  meetTopIsIdentity = andTrueNeutral

BoundedLattice Bool where { }

Lattice Bool where { }

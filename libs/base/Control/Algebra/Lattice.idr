module Control.Algebra.Lattice


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
class JoinSemilattice a where
  join : a -> a -> a

class JoinSemilattice a => VerifiedJoinSemilattice a where
  total joinSemilatticeJoinIsAssociative : (l, c, r : a) -> join l (join c r) = join (join l c) r
  total joinSemilatticeJoinIsCommutative : (l, r : a)    -> join l r = join r l
  total joinSemilatticeJoinIsIdempotent  : (e : a)       -> join e e = e

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
class MeetSemilattice a where
  meet : a -> a -> a

class MeetSemilattice a => VerifiedMeetSemilattice a where
  total meetSemilatticeMeetIsAssociative : (l, c, r : a) -> meet l (meet c r) = meet (meet l c) r
  total meetSemilatticeMeetIsCommutative : (l, r : a)    -> meet l r = meet r l
  total meetSemilatticeMeetIsIdempotent  : (e : a)       -> meet e e = e

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
class JoinSemilattice a => BoundedJoinSemilattice a where
  bottom  : a

class (VerifiedJoinSemilattice a, BoundedJoinSemilattice a) => VerifiedBoundedJoinSemilattice a where
  total boundedJoinSemilatticeBottomIsBottom : (e : a) -> join e bottom = e

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
class MeetSemilattice a => BoundedMeetSemilattice a where
  top : a

class (VerifiedMeetSemilattice a, BoundedMeetSemilattice a) => VerifiedBoundedMeetSemilattice a where
  total boundedMeetSemilatticeTopIsTop : (e : a) -> meet e top = e

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
class (JoinSemilattice a, MeetSemilattice a) => Lattice a where { }

class (VerifiedJoinSemilattice a, VerifiedMeetSemilattice a) => VerifiedLattice a where
  total latticeMeetAbsorbsJoin : (l, r : a) -> meet l (join l r) = l
  total latticeJoinAbsorbsMeet : (l, r : a) -> join l (meet l r) = l

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
class (BoundedJoinSemilattice a, BoundedMeetSemilattice a) => BoundedLattice a where { }

class (VerifiedBoundedJoinSemilattice a, VerifiedBoundedMeetSemilattice a, VerifiedLattice a) => VerifiedBoundedLattice a where { }


instance MeetSemilattice Nat where
  meet = minimum

instance JoinSemilattice Nat where
  join = maximum

instance Lattice Nat where { }

instance BoundedJoinSemilattice Nat where
  bottom = Z

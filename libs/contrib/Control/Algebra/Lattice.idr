module Control.Algebra.Lattice

import Control.Algebra
import Data.Heap

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

implementation JoinSemilattice Nat where
  join = maximum

implementation Ord a => JoinSemilattice (MaxiphobicHeap a) where
  join = merge

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

implementation MeetSemilattice Nat where
  meet = minimum

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

implementation BoundedJoinSemilattice Nat where
  bottom = Z

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

implementation Lattice Nat where { }

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

module Control.Algebra

infixl 6 <->
infixl 7 <.>

%access public export

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
interface Monoid a => Group a where
  inverse : a -> a

(<->) : Group a => a -> a -> a
(<->) left right = left <+> (inverse right)

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
||| + Distributivity of `<.>` and `<+>`:
|||     forall a b c, a <.> (b <+> c) == (a <.> b) <+> (a <.> c)
|||     forall a b c, (a <+> b) <.> c == (a <.> c) <+> (b <.> c)
interface Group a => Ring a where
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
||| + Distributivity of `<.>` and `<+>`:
|||     forall a b c, a <.> (b <+> c) == (a <.> b) <+> (a <.> c)
|||     forall a b c, (a <+> b) <.> c == (a <.> c) <+> (b <.> c)
interface Ring a => RingWithUnity a where
  unity : a

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
||| + Distributivity of `<.>` and `<+>`:
|||     forall a b c, a <.> (b <+> c) == (a <.> b) <+> (a <.> c)
|||     forall a b c, (a <+> b) <.> c == (a <.> c) <+> (b <.> c)
interface RingWithUnity a => Field a where
  inverseM : (x : a) -> Not (x = Algebra.neutral) -> a

sum' : (Foldable t, Monoid a) => t a -> a
sum' = concat

product' : (Foldable t, RingWithUnity a) => t a -> a
product' = foldr (<.>) unity

pow' : RingWithUnity a => a -> Nat -> a
pow' _ Z     = unity
pow' x (S n) = x <.> pow' x n

-- TODO: This can be more efficient:
-- stimes 5 x = x <+> (x <+> (x <+> (x <+> x)))
--            = x <+> ((x <+> x) <+> (x <+> x))
--            = let y = x <+> x in x <+> (y <+> y)
-- 4 <+>s into 3 <+>
||| Combine `n` copies of a value with `<+>`
stimes : Semigroup a => (n : Nat) -> {auto prf : IsSucc n} -> a -> a
stimes (S Z) x = x
stimes (S (S k)) x = x <+> stimes (S k) x

||| Like `stimes`, but accepting `Z` as argument.
mtimes : Monoid a => (n : Nat) -> a -> a
mtimes Z x = neutral
mtimes (S k) x = stimes (S k) x

-- XXX todo:
--   Structures where "abs" make sense.
--   Euclidean domains, etc.
--   Where to put fromInteger and fromRational?

-- "Verified" Interfaces -----------------

interface Semigroup a => VerifiedSemigroup a where
  semigroupOpIsAssociative : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r

interface (VerifiedSemigroup a, Monoid a) => VerifiedMonoid a where
  monoidNeutralIsNeutralL : (l : a) -> l <+> Algebra.neutral = l
  monoidNeutralIsNeutralR : (r : a) -> Algebra.neutral <+> r = r

interface (VerifiedMonoid a, Group a) => VerifiedGroup a where
  groupInverseIsInverseR : (r : a) -> inverse r <+> r = Algebra.neutral

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
interface VerifiedGroup a => AbelianGroup a where
  abelianGroupOpIsCommutative : (l, r : a) -> l <+> r = r <+> l

interface (AbelianGroup a, Ring a) => VerifiedRing a where
  ringOpIsAssociative   : (l, c, r : a) -> l <.> (c <.> r) = (l <.> c) <.> r
  ringOpIsDistributiveL : (l, c, r : a) -> l <.> (c <+> r) = (l <.> c) <+> (l <.> r)
  ringOpIsDistributiveR : (l, c, r : a) -> (l <+> c) <.> r = (l <.> r) <+> (c <.> r)

interface (VerifiedRing a, RingWithUnity a) => VerifiedRingWithUnity a where
  ringWithUnityIsUnityL : (l : a) -> l <.> Algebra.unity = l
  ringWithUnityIsUnityR : (r : a) -> Algebra.unity <.> r = r

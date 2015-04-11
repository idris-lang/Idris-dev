module Classes.Verified

import Control.Algebra
import Control.Algebra.Lattice
import Control.Algebra.VectorSpace

-- Due to these being basically unused and difficult to implement,
-- they're in contrib for a bit. Once a design is found that lets them
-- be implemented for a number of instances, and we get those
-- implementations, then some of them can move back to base (or even
-- prelude, in the cases of Functor, Applicative, Monad, Semigroup,
-- and Monoid).

class Functor f => VerifiedFunctor (f : Type -> Type) where
  functorIdentity : {a : Type} -> (x : f a) -> map id x = id x
  functorComposition : {a : Type} -> {b : Type} -> (x : f a) ->
                       (g1 : a -> b) -> (g2 : b -> c) ->
                       map (g2 . g1) x = (map g2 . map g1) x



class (Applicative f, VerifiedFunctor f) => VerifiedApplicative (f : Type -> Type) where
  applicativeMap : (x : f a) -> (g : a -> b) ->
                   map g x = pure g <*> x
  applicativeIdentity : (x : f a) -> pure id <*> x = x
  applicativeComposition : (x : f a) -> (g1 : f (a -> b)) -> (g2 : f (b -> c)) ->
                           ((pure (.) <*> g2) <*> g1) <*> x = g2 <*> (g1 <*> x)
  applicativeHomomorphism : (x : a) -> (g : a -> b) ->
                            (<*>) {f} (pure g) (pure x) = pure {f} (g x)
  applicativeInterchange : (x : a) -> (g : f (a -> b)) ->
                           g <*> pure x = pure (\g' : a -> b => g' x) <*> g


class (Monad m, VerifiedApplicative m) => VerifiedMonad (m : Type -> Type) where
  monadApplicative : (mf : m (a -> b)) -> (mx : m a) ->
                     mf <*> mx = mf >>= \f =>
                                 mx >>= \x =>
                                        pure (f x)
  monadLeftIdentity : (x : a) -> (f : a -> m b) -> return x >>= f = f x
  monadRightIdentity : (mx : m a) -> mx >>= return = mx
  monadAssociativity : (mx : m a) -> (f : a -> m b) -> (g : b -> m c) ->
                       (mx >>= f) >>= g = mx >>= (\x => f x >>= g)


class Semigroup a => VerifiedSemigroup a where
  total semigroupOpIsAssociative : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r

instance VerifiedSemigroup (List a) where
  semigroupOpIsAssociative = appendAssociative

--instance VerifiedSemigroup Nat where
--  semigroupOpIsAssociative = plusAssociative


class (VerifiedSemigroup a, Monoid a) => VerifiedMonoid a where
  total monoidNeutralIsNeutralL : (l : a) -> l <+> neutral = l
  total monoidNeutralIsNeutralR : (r : a) -> neutral <+> r = r

-- instance VerifiedMonoid Nat where
--   monoidNeutralIsNeutralL = plusZeroRightNeutral
--   monoidNeutralIsNeutralR = plusZeroLeftNeutral

instance VerifiedMonoid (List a) where
  monoidNeutralIsNeutralL = appendNilRightNeutral
  monoidNeutralIsNeutralR xs = Refl

class (VerifiedMonoid a, Group a) => VerifiedGroup a where
  total groupInverseIsInverseL : (l : a) -> l <+> inverse l = neutral
  total groupInverseIsInverseR : (r : a) -> inverse r <+> r = neutral

class (VerifiedGroup a, AbelianGroup a) => VerifiedAbelianGroup a where
  total abelianGroupOpIsCommutative : (l, r : a) -> l <+> r = r <+> l

class (VerifiedAbelianGroup a, Ring a) => VerifiedRing a where
  total ringOpIsAssociative   : (l, c, r : a) -> l <.> (c <.> r) = (l <.> c) <.> r
  total ringOpIsDistributiveL : (l, c, r : a) -> l <.> (c <+> r) = (l <.> c) <+> (l <.> r)
  total ringOpIsDistributiveR : (l, c, r : a) -> (l <+> c) <.> r = (l <.> r) <+> (c <.> r)

class (VerifiedRing a, RingWithUnity a) => VerifiedRingWithUnity a where
  total ringWithUnityIsUnityL : (l : a) -> l <.> unity = l
  total ringWithUnityIsUnityR : (r : a) -> unity <.> r = r

class (VerifiedRing a, Field a) => VerifiedField a where
  total fieldInverseIsInverseL : (l : a) -> l <.> inverseM l = unity
  total fieldInverseIsInverseR : (r : a) -> inverseM r <.> r = unity


class JoinSemilattice a => VerifiedJoinSemilattice a where
  total joinSemilatticeJoinIsAssociative : (l, c, r : a) -> join l (join c r) = join (join l c) r
  total joinSemilatticeJoinIsCommutative : (l, r : a)    -> join l r = join r l
  total joinSemilatticeJoinIsIdempotent  : (e : a)       -> join e e = e

class MeetSemilattice a => VerifiedMeetSemilattice a where
  total meetSemilatticeMeetIsAssociative : (l, c, r : a) -> meet l (meet c r) = meet (meet l c) r
  total meetSemilatticeMeetIsCommutative : (l, r : a)    -> meet l r = meet r l
  total meetSemilatticeMeetIsIdempotent  : (e : a)       -> meet e e = e

class (VerifiedJoinSemilattice a, BoundedJoinSemilattice a) => VerifiedBoundedJoinSemilattice a where
  total boundedJoinSemilatticeBottomIsBottom : (e : a) -> join e bottom = e

class (VerifiedMeetSemilattice a, BoundedMeetSemilattice a) => VerifiedBoundedMeetSemilattice a where
  total boundedMeetSemilatticeTopIsTop : (e : a) -> meet e top = e

class (VerifiedJoinSemilattice a, VerifiedMeetSemilattice a) => VerifiedLattice a where
  total latticeMeetAbsorbsJoin : (l, r : a) -> meet l (join l r) = l
  total latticeJoinAbsorbsMeet : (l, r : a) -> join l (meet l r) = l

class (VerifiedBoundedJoinSemilattice a, VerifiedBoundedMeetSemilattice a, VerifiedLattice a) => VerifiedBoundedLattice a where { }


class (VerifiedRingWithUnity a, VerifiedAbelianGroup b, Module a b) => VerifiedModule a b where
  total moduleScalarMultiplyComposition : (x,y : a) -> (v : b) -> x <#> (y <#> v) = (x <.> y) <#> v
  total moduleScalarUnityIsUnity : (v : b) -> unity {a} <#> v = v
  total moduleScalarMultDistributiveWRTVectorAddition : (s : a) -> (v, w : b) -> s <#> (v <+> w) = (s <#> v) <+> (s <#> w)
  total moduleScalarMultDistributiveWRTModuleAddition : (s, t : a) -> (v : b) -> (s <+> t) <#> v = (s <#> v) <+> (t <#> v)

class (VerifiedField a, VerifiedModule a b) => VerifiedVectorSpace a b where {}

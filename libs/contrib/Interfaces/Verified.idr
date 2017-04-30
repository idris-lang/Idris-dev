module Interfaces.Verified

import Control.Algebra
import Control.Algebra.Lattice
import Control.Algebra.NumericImplementations
import Control.Algebra.VectorSpace
import Data.ZZ

%access public export

-- Due to these being basically unused and difficult to implement,
-- they're in contrib for a bit. Once a design is found that lets them
-- be implemented for a number of implementations, and we get those
-- implementations, then some of them can move back to base (or even
-- prelude, in the cases of Functor, Applicative, Monad, Semigroup,
-- and Monoid).

interface Functor f => VerifiedFunctor (f : Type -> Type) where
  functorIdentity : {a : Type} -> (x : f a) -> map Basics.id x = Basics.id x
  functorComposition : {a : Type} -> {b : Type} -> (x : f a) ->
                       (g1 : a -> b) -> (g2 : b -> c) ->
                       map (g2 . g1) x = (map g2 . map g1) x

-- TODO VerifiedFunctor instances for: List, Stream, Either e

VerifiedFunctor Maybe where
  functorIdentity Nothing = Refl
  functorIdentity (Just x) = Refl
  functorComposition Nothing g1 g2 = Refl
  functorComposition (Just x) g1 g2 = Refl

interface (Applicative f, VerifiedFunctor f) => VerifiedApplicative (f : Type -> Type) where
  applicativeMap : (x : f a) -> (g : a -> b) ->
                   map g x = pure g <*> x
  applicativeIdentity : (x : f a) -> pure Basics.id <*> x = x
  applicativeComposition : (x : f a) -> (g1 : f (a -> b)) -> (g2 : f (b -> c)) ->
                           ((pure (.) <*> g2) <*> g1) <*> x = g2 <*> (g1 <*> x)
  applicativeHomomorphism : (x : a) -> (g : a -> b) ->
                            (<*>) {f} (pure g) (pure x) = pure {f} (g x)
  applicativeInterchange : (x : a) -> (g : f (a -> b)) ->
                           g <*> pure x = pure (\g' : (a -> b) => g' x) <*> g

VerifiedApplicative Maybe where
  applicativeMap Nothing g = Refl
  applicativeMap (Just x) g = Refl
  applicativeIdentity Nothing = Refl
  applicativeIdentity (Just x) = Refl
  applicativeComposition Nothing Nothing Nothing = Refl
  applicativeComposition Nothing Nothing (Just x) = Refl
  applicativeComposition Nothing (Just x) Nothing = Refl
  applicativeComposition Nothing (Just x) (Just y) = Refl
  applicativeComposition (Just x) Nothing Nothing = Refl
  applicativeComposition (Just x) Nothing (Just y) = Refl
  applicativeComposition (Just x) (Just y) Nothing = Refl
  applicativeComposition (Just x) (Just y) (Just z) = Refl
  applicativeHomomorphism x g = Refl
  applicativeInterchange x Nothing = Refl
  applicativeInterchange x (Just y) = Refl

-- TODO VerifiedApplicative instances for: List, Stream, Either e

interface (Monad m, VerifiedApplicative m) => VerifiedMonad (m : Type -> Type) where
  monadApplicative : (mf : m (a -> b)) -> (mx : m a) ->
                     mf <*> mx = mf >>= \f =>
                                 mx >>= \x =>
                                        pure (f x)
  monadLeftIdentity : (x : a) -> (f : a -> m b) -> pure x >>= f = f x
  monadRightIdentity : (mx : m a) -> mx >>= Applicative.pure = mx
  monadAssociativity : (mx : m a) -> (f : a -> m b) -> (g : b -> m c) ->
                       (mx >>= f) >>= g = mx >>= (\x => f x >>= g)

VerifiedMonad Maybe where
    monadApplicative Nothing Nothing = Refl
    monadApplicative Nothing (Just x) = Refl
    monadApplicative (Just x) Nothing = Refl
    monadApplicative (Just x) (Just y) = Refl
    monadLeftIdentity x f = Refl
    monadRightIdentity Nothing = Refl
    monadRightIdentity (Just x) = Refl
    monadAssociativity Nothing f g = Refl
    monadAssociativity (Just x) f g = Refl

-- TODO VerifiedMonad instances for: List, Stream, Either e

interface Semigroup a => VerifiedSemigroup a where
  total semigroupOpIsAssociative : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r

implementation VerifiedSemigroup (List a) where
  semigroupOpIsAssociative = appendAssociative

[PlusNatSemiV] VerifiedSemigroup Nat using PlusNatSemi where
  semigroupOpIsAssociative = plusAssociative

[MultNatSemiV] VerifiedSemigroup Nat using MultNatSemi where
  semigroupOpIsAssociative = multAssociative

[PlusZZSemiV] VerifiedSemigroup ZZ using PlusZZSemi where
  semigroupOpIsAssociative = plusAssociativeZ

[MultZZSemiV] VerifiedSemigroup ZZ using MultZZSemi where
  semigroupOpIsAssociative = multAssociativeZ

-- TODO Verified versions of...
--  (Semigroup m, Semigroup n) => Semigroup (m, n) where
--    (a, b) <+> (c, d) = (a <+> c, b <+> d)
--
-- Semigroup (Maybe a)
--
-- [collectJust] Semigroup a => Semigroup (Maybe a)
--
-- libs/base/Data/Morphisms.idr: implementation Monoid (Endomorphism a)

interface (VerifiedSemigroup a, Monoid a) => VerifiedMonoid a where
  total monoidNeutralIsNeutralL : (l : a) -> l <+> Algebra.neutral = l
  total monoidNeutralIsNeutralR : (r : a) -> Algebra.neutral <+> r = r

[PlusNatMonoidV] VerifiedMonoid Nat using PlusNatSemiV, PlusNatMonoid where
   monoidNeutralIsNeutralL = plusZeroRightNeutral
   monoidNeutralIsNeutralR = plusZeroLeftNeutral

[MultNatMonoidV] VerifiedMonoid Nat using MultNatSemiV, MultNatMonoid where
  monoidNeutralIsNeutralL = multOneRightNeutral
  monoidNeutralIsNeutralR = multOneLeftNeutral

[PlusZZMonoidV] VerifiedMonoid ZZ using PlusZZSemiV, PlusZZMonoid where
   monoidNeutralIsNeutralL = plusZeroRightNeutralZ
   monoidNeutralIsNeutralR = plusZeroLeftNeutralZ

[MultZZMonoidV] VerifiedMonoid ZZ using MultZZSemiV, MultZZMonoid where
  monoidNeutralIsNeutralL = multOneRightNeutralZ
  monoidNeutralIsNeutralR = multOneLeftNeutralZ

implementation VerifiedMonoid (List a) where
  monoidNeutralIsNeutralL = appendNilRightNeutral
  monoidNeutralIsNeutralR xs = Refl

-- TODO Verified versions of...
--  (Monoid m, Monoid n) => Monoid (m, n) where
--    neutral = (neutral, neutral)
--
-- Monoid (Maybe a)

interface (VerifiedMonoid a, Group a) => VerifiedGroup a where
  total groupInverseIsInverseL : (l : a) -> l <+> inverse l = Algebra.neutral
  total groupInverseIsInverseR : (r : a) -> inverse r <+> r = Algebra.neutral

VerifiedGroup ZZ using PlusZZMonoidV where
  groupInverseIsInverseL k = rewrite sym $ multCommutativeZ (NegS 0) k in
                             rewrite multNegLeftZ 0 k in
                             rewrite multOneLeftNeutralZ k in
                             plusNegateInverseLZ k
  groupInverseIsInverseR k = rewrite sym $ multCommutativeZ (NegS 0) k in
                             rewrite multNegLeftZ 0 k in
                             rewrite multOneLeftNeutralZ k in
                             plusNegateInverseRZ k

interface (VerifiedGroup a, AbelianGroup a) => VerifiedAbelianGroup a where
  total abelianGroupOpIsCommutative : (l, r : a) -> l <+> r = r <+> l

VerifiedAbelianGroup ZZ where
  abelianGroupOpIsCommutative = plusCommutativeZ

interface (VerifiedAbelianGroup a, Ring a) => VerifiedRing a where
  total ringOpIsAssociative   : (l, c, r : a) -> l <.> (c <.> r) = (l <.> c) <.> r
  total ringOpIsDistributiveL : (l, c, r : a) -> l <.> (c <+> r) = (l <.> c) <+> (l <.> r)
  total ringOpIsDistributiveR : (l, c, r : a) -> (l <+> c) <.> r = (l <.> r) <+> (c <.> r)

VerifiedRing ZZ where
  ringOpIsAssociative = multAssociativeZ
  ringOpIsDistributiveL = multDistributesOverPlusRightZ
  ringOpIsDistributiveR = multDistributesOverPlusLeftZ

interface (VerifiedRing a, RingWithUnity a) => VerifiedRingWithUnity a where
  total ringWithUnityIsUnityL : (l : a) -> l <.> Algebra.unity = l
  total ringWithUnityIsUnityR : (r : a) -> Algebra.unity <.> r = r

VerifiedRingWithUnity ZZ where
  ringWithUnityIsUnityL = multOneRightNeutralZ
  ringWithUnityIsUnityR = multOneLeftNeutralZ

--interface (VerifiedRingWithUnity a, Field a) => VerifiedField a where
--  total fieldInverseIsInverseL : (l : a) -> (notId : Not (l = Algebra.neutral)) -> l <.> (inverseM l notId) = Algebra.unity
--  total fieldInverseIsInverseR : (r : a) -> (notId : Not (r = Algebra.neutral)) -> (inverseM r notId) <.> r = Algebra.unity

interface JoinSemilattice a => VerifiedJoinSemilattice a where
  total joinSemilatticeJoinIsAssociative : (l, c, r : a) -> join l (join c r) = join (join l c) r
  total joinSemilatticeJoinIsCommutative : (l, r : a)    -> join l r = join r l
  total joinSemilatticeJoinIsIdempotent  : (e : a)       -> join e e = e

interface MeetSemilattice a => VerifiedMeetSemilattice a where
  total meetSemilatticeMeetIsAssociative : (l, c, r : a) -> meet l (meet c r) = meet (meet l c) r
  total meetSemilatticeMeetIsCommutative : (l, r : a)    -> meet l r = meet r l
  total meetSemilatticeMeetIsIdempotent  : (e : a)       -> meet e e = e

{- FIXME: Some maintenance required here.
   Algebra.top and Algebra.bottom don't exist!
-}
{-

interface (VerifiedJoinSemilattice a, BoundedJoinSemilattice a) => VerifiedBoundedJoinSemilattice a where
  total boundedJoinSemilatticeBottomIsBottom : (e : a) -> join e Algebra.bottom = e

interface (VerifiedMeetSemilattice a, BoundedMeetSemilattice a) => VerifiedBoundedMeetSemilattice a where
  total boundedMeetSemilatticeTopIsTop : (e : a) -> meet e Algebra.top = e

interface (VerifiedJoinSemilattice a, VerifiedMeetSemilattice a) => VerifiedLattice a where
  total latticeMeetAbsorbsJoin : (l, r : a) -> meet l (join l r) = l
  total latticeJoinAbsorbsMeet : (l, r : a) -> join l (meet l r) = l

interface (VerifiedBoundedJoinSemilattice a, VerifiedBoundedMeetSemilattice a, VerifiedLattice a) => VerifiedBoundedLattice a where { }


--interface (VerifiedRingWithUnity a, VerifiedAbelianGroup b, Module a b) => VerifiedModule a b where
--  total moduleScalarMultiplyComposition : (x,y : a) -> (v : b) -> x <#> (y <#> v) = (x <.> y) <#> v
--  total moduleScalarUnityIsUnity : (v : b) -> Algebra.unity {a} <#> v = v
--  total moduleScalarMultDistributiveWRTVectorAddition : (s : a) -> (v, w : b) -> s <#> (v <+> w) = (s <#> v) <+> (s <#> w)
--  total moduleScalarMultDistributiveWRTModuleAddition : (s, t : a) -> (v : b) -> (s <+> t) <#> v = (s <#> v) <+> (t <#> v)

--interface (VerifiedField a, VerifiedModule a b) => VerifiedVectorSpace a b where {}

-}

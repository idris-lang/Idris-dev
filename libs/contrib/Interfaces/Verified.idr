module Interfaces.Verified

import Control.Algebra.Lattice

%default total
%access public export

----------------------------------------

interface Functor f => VerifiedFunctor (f : Type -> Type) where
  functorIdentity : {a : Type} -> (g : a -> a) -> ((v : a) -> g v = v) -> (x : f a) -> map g x = x
  functorComposition : {a : Type} -> {b : Type} -> (x : f a) ->
                       (g1 : a -> b) -> (g2 : b -> c) ->
                       map (g2 . g1) x = (map g2 . map g1) x

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

interface (Monad m, VerifiedApplicative m) => VerifiedMonad (m : Type -> Type) where
  monadApplicative : (mf : m (a -> b)) -> (mx : m a) ->
                     mf <*> mx = mf >>= \f =>
                                 mx >>= \x =>
                                        pure (f x)
  monadLeftIdentity : (x : a) -> (f : a -> m b) -> pure x >>= f = f x
  monadRightIdentity : (mx : m a) -> mx >>= Applicative.pure = mx
  monadAssociativity : (mx : m a) -> (f : a -> m b) -> (g : b -> m c) ->
                       (mx >>= f) >>= g = mx >>= (\x => f x >>= g)

interface (Alternative f, VerifiedApplicative f) => VerifiedAlternative (f : Type -> Type) where
  alternativeLeftIdentity : (x : f a) -> Applicative.empty <|> x = x
  alternativeRightIdentity : (x : f a) -> x <|> Applicative.empty = x
  alternativeAssociativity : (x : f a) -> (y : f a) -> (z : f a) ->
                             x <|> (y <|> z) = (x <|> y) <|> z

----------------------------------------

interface JoinSemilattice a => VerifiedJoinSemilattice a where
  joinSemilatticeJoinIsAssociative : (l, c, r : a) -> join l (join c r) = join (join l c) r
  joinSemilatticeJoinIsCommutative : (l, r : a)    -> join l r = join r l
  joinSemilatticeJoinIsIdempotent  : (e : a)       -> join e e = e

interface MeetSemilattice a => VerifiedMeetSemilattice a where
  meetSemilatticeMeetIsAssociative : (l, c, r : a) -> meet l (meet c r) = meet (meet l c) r
  meetSemilatticeMeetIsCommutative : (l, r : a)    -> meet l r = meet r l
  meetSemilatticeMeetIsIdempotent  : (e : a)       -> meet e e = e

interface (VerifiedJoinSemilattice a, BoundedJoinSemilattice a) => VerifiedBoundedJoinSemilattice a where
  joinBottomIsIdentity : (x : a) -> join x Lattice.bottom = x

interface (VerifiedMeetSemilattice a, BoundedMeetSemilattice a) => VerifiedBoundedMeetSemilattice a where
  meetTopIsIdentity : (x : a) -> meet x Lattice.top = x

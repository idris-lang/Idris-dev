module Data.Morphisms

%default total
%access public export

record Morphism a b where
  constructor Mor
  applyMor : a -> b
infixr 1 ~>
(~>) : Type -> Type -> Type
(~>) = Morphism

record Endomorphism a where
  constructor Endo
  applyEndo : a -> a

record Kleislimorphism (f : Type -> Type) a b where
  constructor Kleisli
  applyKleisli : a -> f b

Functor (Morphism r) where
  map f (Mor a) = Mor $ f . a

Applicative (Morphism r) where
  pure a = Mor $ const a
  (Mor f) <*> (Mor a) = Mor $ \r => f r $ a r

Monad (Morphism r) where
  (Mor h) >>= f = Mor $ \r => applyMor (f $ h r) r

-- Postulates --------------------------

-- These are required for implementing verified interfaces.
-- TODO : Prove them.

postulate private
morphism_assoc : Semigroup a => (f, g, h : r -> a) ->
  Mor (\r => f r <+> (g r <+> h r)) = Mor (\r => f r <+> g r <+> h r)

postulate private
morphism_neutl : Monoid a => (f : r -> a) ->
  Mor (\r => f r <+> Prelude.Algebra.neutral) = Mor f

postulate private
morphism_neutr : Monoid a => (f : r -> a) ->
  Mor (\r => Prelude.Algebra.neutral <+> f r) = Mor f

postulate private
kleisli_assoc : (Semigroup a, Applicative f) => (i, j, k : s -> f a) ->
   Kleisli (\r => pure (<+>) <*> i r <*> (pure (<+>) <*> j r <*> k r)) =
     Kleisli (\r => pure (<+>) <*> (pure (<+>) <*> i r <*> j r) <*> k r)

postulate private
kleisli_neutl : (Monoid a, Applicative f) => (g : r -> f a) ->
  Kleisli (\x => pure (<+>) <*> g x <*> pure Prelude.Algebra.neutral) = Kleisli g

postulate private
kleisli_neutr : (Monoid a, Applicative f) => (g : r -> f a) ->
  Kleisli (\x => pure (<+>) <*> pure Prelude.Algebra.neutral <*> g x) = Kleisli g

----------------------------------------

Semigroup a => Semigroup (Morphism r a) where
  f <+> g = [| f <+> g |]

  semigroupOpIsAssociative (Mor f) (Mor g) (Mor h) = morphism_assoc f g h

Monoid a => Monoid (Morphism r a) where
  neutral = [| neutral |]

  monoidNeutralIsNeutralL (Mor f) = morphism_neutl f
  monoidNeutralIsNeutralR (Mor f) = morphism_neutr f

Semigroup (Endomorphism a) where
  (Endo f) <+> (Endo g) = Endo $ g . f

  semigroupOpIsAssociative (Endo _) (Endo _) (Endo _) = Refl

Monoid (Endomorphism a) where
  neutral = Endo id

  monoidNeutralIsNeutralL (Endo _) = Refl
  monoidNeutralIsNeutralR (Endo _) = Refl

Functor f => Functor (Kleislimorphism f a) where
  map f (Kleisli g) = Kleisli (map f . g)

Applicative f => Applicative (Kleislimorphism f a) where
  pure a = Kleisli $ const $ pure a
  (Kleisli f) <*> (Kleisli a) = Kleisli $ \r => f r <*> a r

Monad f => Monad (Kleislimorphism f a) where
  (Kleisli f) >>= g = Kleisli $ \r => applyKleisli (g !(f r)) r

-- Applicative is a bit too strong, but there is no suitable superclass
(Semigroup a, Applicative f) => Semigroup (Kleislimorphism f s a) where
  f <+> g = [| f <+> g |]

  semigroupOpIsAssociative (Kleisli i) (Kleisli j) (Kleisli k) = kleisli_assoc i j k

(Monoid a, Applicative f) => Monoid (Kleislimorphism f r a) where
  neutral = [| neutral |]

  monoidNeutralIsNeutralL (Kleisli g) = kleisli_neutl g
  monoidNeutralIsNeutralR (Kleisli g) = kleisli_neutr g

Cast (Endomorphism a) (Morphism a a) where
  cast (Endo f) = Mor f

Cast (Morphism a a) (Endomorphism a) where
  cast (Mor f) = Endo f

Cast (Morphism a (f b)) (Kleislimorphism f a b) where
  cast (Mor f) = Kleisli f

Cast (Kleislimorphism f a b) (Morphism a (f b)) where
  cast (Kleisli f) = Mor f

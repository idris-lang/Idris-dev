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

Semigroup a => Semigroup (Morphism r a) where
  f <+> g = [| f <+> g |]

Monoid a => Monoid (Morphism r a) where
  neutral = [| neutral |]

Semigroup (Endomorphism a) where
  (Endo f) <+> (Endo g) = Endo $ g . f

Monoid (Endomorphism a) where
  neutral = Endo id

Functor f => Functor (Kleislimorphism f a) where
  map f (Kleisli g) = Kleisli (map f . g)

Applicative f => Applicative (Kleislimorphism f a) where
  pure a = Kleisli $ const $ pure a
  (Kleisli f) <*> (Kleisli a) = Kleisli $ \r => f r <*> a r

Monad f => Monad (Kleislimorphism f a) where
  (Kleisli f) >>= g = Kleisli $ \r => applyKleisli (g !(f r)) r

-- Applicative is a bit too strong, but there is no suitable superclass
(Semigroup a, Applicative f) => Semigroup (Kleislimorphism f r a) where
  f <+> g = [| f <+> g |]

(Monoid a, Applicative f) => Monoid (Kleislimorphism f r a) where
  neutral = [| neutral |]

Cast (Endomorphism a) (Morphism a a) where
  cast (Endo f) = Mor f

Cast (Morphism a a) (Endomorphism a) where
  cast (Mor f) = Endo f

Cast (Morphism a (f b)) (Kleislimorphism f a b) where
  cast (Mor f) = Kleisli f

Cast (Kleislimorphism f a b) (Morphism a (f b)) where
  cast (Kleisli f) = Mor f

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

Semigroup (Endomorphism a) where
  (Endo f) <+> (Endo g) = Endo $ g . f

Monoid (Endomorphism a) where
  neutral = Endo id

Cast (Endomorphism a) (Morphism a a) where
  cast (Endo f) = Mor f

Cast (Morphism a a) (Endomorphism a) where
  cast (Mor f) = Endo f

Cast (Morphism a (f b)) (Kleislimorphism f a b) where
  cast (Mor f) = Kleisli f

Cast (Kleislimorphism f a b) (Morphism a (f b)) where
  cast (Kleisli f) = Mor f

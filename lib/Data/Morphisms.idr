module Data.Morphisms

import Builtins

%access public

data Homomorphism : Type -> Type -> Type where
  Homo : (a -> b) -> Homomorphism a b

data Endomorphism : Type -> Type where
  Endo : (a -> a) -> Endomorphism a

data Kleislimorphism : (Type -> Type) -> Type -> Type -> Type where
  Kleisli : Monad m => (a -> m b) -> Kleislimorphism m a b

applyKleisli : Monad m => (Kleislimorphism m a b) -> a -> m b
applyKleisli (Kleisli f) a = f a

applyHomo : Homomorphism a b -> a -> b
applyHomo (Homo f) a = f a

applyEndo : Endomorphism a -> a -> a
applyEndo (Endo f) a = f a

instance Functor (Homomorphism r) where
  fmap f (Homo a) = Homo (f . a)

instance Applicative (Homomorphism r) where
  pure a                = Homo $ const a
  (Homo f) <$> (Homo a) = Homo $ \r => f r $ a r

instance Monad (Homomorphism r) where
  return a       = Homo $ const a
  (Homo h) >>= f = Homo $ \r => applyHomo (f $ h r) r

instance Semigroup (Endomorphism a) where
  (Endo f) <+> (Endo g) = Endo $ g . f

instance Monoid (Endomorphism a) where
  neutral = Endo id

infixr 1 ~>

(~>) : Type -> Type -> Type
a ~> b = Homomorphism a b

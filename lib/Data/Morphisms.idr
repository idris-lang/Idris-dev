module Data.Morphisms

%access public

data Homomorphism : Set -> Set -> Set where
  Homo : (a -> b) -> Homomorphism a b

data Endomorphism : Set -> Set where
  Endo : (a -> a) -> Endomorphism a

data Kleislimorphism : (Set -> Set) -> Set -> Set -> Set where
  Kleisli : Monad m => (a -> m b) -> Kleislimorphism m a b

runKleisli : Monad m => (Kleislimorphism m a b) -> a -> m b
runKleisli (Kleisli f) a = f a

namespace Homo
  ($) : Homomorphism a b -> a -> b
  (Homo f) $ a = f a

namespace Endo
  ($) : Endomorphism a -> a -> a
  (Endo f) $ a = f a

instance Monad (Homomorphism r) where
  return a       = Homo $ const a
  (Homo h) >>= f = Homo $ \r => f (h r) $ r

instance Applicative (Homomorphism r) where
  pure a                = Homo $ const a
  (Homo f) <$> (Homo a) = Homo $ \r => f r $ a r

instance Semigroup (Endomorphism a) where
  (Endo f) <+> (Endo g) = Endo $ g . f

instance Monoid (Endomorphism a) where
  neutral = Endo id

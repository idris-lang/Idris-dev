module Data.Morphisms

%access public

data Homomorphism : Set -> Set -> Set where
  Homo : (a -> b) -> Homomorphism a b

($) : Morphism a b -> a -> b
(Homo f) $ a = f a

($) : Homomorphism a b -> a -> b
(Homo f) $ a = f a

instance Monad (Homomorphism r) where
  return a       = Homo $ const a
  (Homo h) >>= f = Homo $ \r => f (h r) $ r

instance Applicative (Homomorphism r) where
  pure a                = Homo $ const a
  (Homo f) <$> (Homo a) = Homo $ \r => f r $ a r

infixr 1 ~>

(~>) : Set -> Set -> Set
a ~> b = Morphism a b

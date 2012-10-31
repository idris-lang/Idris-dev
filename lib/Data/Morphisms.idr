module Data.Morphisms

%access public

data Morphism : Set -> Set -> Set where
    Homo : (a -> b) -> Morphism a b

($) : Morphism a b -> a -> b
(Homo f) $ a = f a

instance Monad (Morphism r) where
  return a       = Homo $ const a
  (Homo h) >>= f = Homo $ \r => f (h r) $ r

instance Applicative (Morphism r) where
  pure a                = Homo $ const a
  (Homo f) <$> (Homo a) = Homo $ \r => f r $ a r

infixr 1 ~>

(~>) : Set -> Set -> Set
a ~> b = Morphism a b

module Providers

public
data Provider a = Provide a | Error String

-- instances
instance Functor Provider where
  map f (Provide a) = Provide (f a)
  map f (Error err) = Error err

instance Applicative Provider where
  (Provide f) <$> (Provide x) = Provide (f x)
  (Provide f) <$> (Error err) = Error err
  (Error err) <$> _ = Error err
  pure = Provide

instance Monad Provider where
  (Provide x) >>= f = f x
  (Error err) >>= _ = Error err

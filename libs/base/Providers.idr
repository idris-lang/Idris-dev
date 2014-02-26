module Providers

public
data Provider a = Provide a | Error String | Postulate

-- instances
instance Functor Provider where
  map f (Provide a) = Provide (f a)
  map f (Error err) = Error err
  map f Postulate   = Postulate

instance Applicative Provider where
  (Provide f) <$> (Provide x) = Provide (f x)
  (Provide f) <$> (Error err) = Error err
  (Provide f) <$> Postulate   = Postulate
  (Error err) <$> _           = Error err
  Postulate   <$> (Error err) = Error err
  Postulate   <$> _           = Postulate
  pure = Provide

-- is this correct for Postulate?
instance Monad Provider where
  (Provide x) >>= f = f x
  (Error err) >>= _ = Error err
  Postulate   >>= f = Postulate

module Providers

||| Type providers must build one of these in an IO computation.
public
data Provider : (a : Type) -> Type where
  ||| Return a term to be spliced in
  ||| @ x the term to be spliced (i.e. the proof)
  Provide : (x : a) -> Provider a

  ||| Report an error to the user and stop compilation
  ||| @ msg the error message
  Error : (msg : String) -> Provider a

-- instances
instance Functor Provider where
  map f (Provide a) = Provide (f a)
  map f (Error err) = Error err

instance Applicative Provider where
  (Provide f) <$> (Provide x) = Provide (f x)
  (Provide f) <$> (Error err) = Error err
  (Error err) <$> _           = Error err
  pure = Provide

instance Monad Provider where
  (Provide x) >>= f = f x
  (Error err) >>= _ = Error err

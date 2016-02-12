module Prelude.Providers

import Prelude.Basics
import Prelude.Functor
import Prelude.Applicative
import Prelude.Monad

%access public export

||| Type providers must build one of these in an IO computation.
public export
data Provider : (a : Type) -> Type where
  ||| Return a term to be spliced in
  ||| @ x the term to be spliced (i.e. the proof)
  Provide : (x : a) -> Provider a

  ||| Report an error to the user and stop compilation
  ||| @ msg the error message
  Error : (msg : String) -> Provider a

Functor Provider where
  map f (Provide a) = Provide (f a)
  map f (Error err) = Error err

Applicative Provider where
  (Provide f) <*> (Provide x) = Provide (f x)
  (Provide f) <*> (Error err) = Error err
  (Error err) <*> _           = Error err
  pure = Provide

Monad Provider where
  (Provide x) >>= f = f x
  (Error err) >>= _ = Error err

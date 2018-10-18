||| Utilities for working with types, containing no more than one value.
module Prelude.Singleton

import Builtins
import Prelude.Uninhabited

%default total
%access public export

||| A canonical proof that some type containing no more than one value
interface Singleton t where
  ||| If I have two values of t, prove that they are actually the same
  single : (x : t) -> (y : t) -> x = y

Singleton () where
  single () () = Refl

Singleton (x = y) where
  single Refl Refl = Refl

Singleton Void where
  single _ _ impossible

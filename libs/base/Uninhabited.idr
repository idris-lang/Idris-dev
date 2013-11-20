module Uninhabited

import Prelude

class Uninhabited t where
  total uninhabited : t -> _|_

instance Uninhabited (Fin Z) where
  uninhabited fZ impossible
  uninhabited (fS f) impossible

instance Uninhabited (Z = S n) where
  uninhabited refl impossible


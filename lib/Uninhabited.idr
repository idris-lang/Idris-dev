module Uninhabited

class Uninhabited t where
  total uninhabited : t -> _|_

instance Uninhabited (Fin O) where
  uninhabited fO impossible
  uninhabited (fS f) impossible

instance Uninhabited (O = S n) where
  uninhabited refl impossible


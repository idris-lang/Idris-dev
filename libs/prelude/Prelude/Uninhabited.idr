module Prelude.Uninhabited

class Uninhabited t where
  total uninhabited : t -> _|_

instance Uninhabited (Fin Z) where
  uninhabited fZ impossible
  uninhabited (fS f) impossible

instance Uninhabited (Z = S n) where
  uninhabited refl impossible

||| Use an absurd assumption to discharge a proof obligation
absurd : Uninhabited t => t -> a
absurd t = FalseElim (uninhabited t)

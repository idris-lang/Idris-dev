module Prelude.Uninhabited

import Builtins

||| A canonical proof that some type is empty
class Uninhabited t where
  ||| If I have a t, I've had a contradiction
  ||| @ t the uninhabited type
  total uninhabited : t -> _|_

||| Use an absurd assumption to discharge a proof obligation
||| @ t some empty type
||| @ a the goal type
||| @ h the contradictory hypothesis
absurd : Uninhabited t => (h : t) -> a
absurd h = FalseElim (uninhabited h)

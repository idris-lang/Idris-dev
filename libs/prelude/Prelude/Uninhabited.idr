||| Utilities for working with uninhabited types, to record explicit
||| locations for canonical proofs of emptiness. Typically, one should
||| use the `absurd` function.
module Prelude.Uninhabited

import Builtins

%access public export

||| A canonical proof that some type is empty
interface Uninhabited t where
  ||| If I have a t, I've had a contradiction
  ||| @ t the uninhabited type
  total uninhabited : t -> Void

Uninhabited Void where
  uninhabited a = a

||| Use an absurd assumption to discharge a proof obligation
||| @ t some empty type
||| @ a the goal type
||| @ h the contradictory hypothesis
absurd : Uninhabited t => (h : t) -> a
absurd h = void (uninhabited h)

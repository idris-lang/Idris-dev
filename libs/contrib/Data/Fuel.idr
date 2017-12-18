module Data.Fuel

%access public export
%default total

||| Fuel for running total operations potentially indefinitely.
data Fuel = Dry | More (Lazy Fuel)

||| Provide `n` units of fuel.
limit : Nat -> Fuel
limit Z = Dry
limit (S n) = More (limit n)

||| Provide fuel indefinitely.
||| This function is fundamentally partial.
partial
forever : Fuel
forever = More forever

||| Utilities functions for contitionally delaying values.
module Control.Delayed

%default total

||| Type-level function for a conditionally delayed type (`Lazy` or `Inf`).
public export
delayed : DelayReason -> Bool -> Type -> Type
delayed r False a = a
delayed r True a = Delayed r a

||| Type-level function for a conditionally infinite type.
public export
inf : Bool -> Type -> Type
inf = delayed Infinite

||| Type-level function for a conditionally lazy type.
public export
lazy : Bool -> Type -> Type
lazy = delayed LazyValue

||| Conditionally delay a value.
export
delay : (d : Bool) -> a -> delayed r d a
delay False x = x
delay True x = Delay x

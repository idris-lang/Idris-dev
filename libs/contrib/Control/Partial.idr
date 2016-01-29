||| Control structures that are fundamentally partial
module Control.Partial


||| Repeatedly apply `f` to `v` until `p` is `True`.
|||
||| @ p the predicate to wait for
||| @ f the function to repeatedly apply
||| @ v the starting value
partial export
until : (p : a -> Bool) -> (f : a -> a) -> (v : a) -> a
until p f v with (p v)
  | False = until p f (f v)
  | True = v

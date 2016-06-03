%default total

InterpBool : () -> Type
InterpBool () = {x : Type} -> x -> Nat

interface IdrisBug (u : ()) where
  idrisBug : InterpBool u

implementation IdrisBug () where
  idrisBug _ = Z

f : Nat
f = idrisBug {u = ()} 'a'


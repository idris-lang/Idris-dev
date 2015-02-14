%default total

InterpBool : () -> Type
InterpBool () = {x : Type} -> x -> Nat

class IdrisBug (u : ()) where
  idrisBug : InterpBool u

instance IdrisBug () where
  idrisBug _ = Z

f : Nat
f = idrisBug {u = ()} 'a'


module Mod

-- %access public

export
natfn : Nat -> Nat
natfn n = (S (S n))

public export
natexp : (n : Nat) -> Nat
natexp k = S (natfn k)


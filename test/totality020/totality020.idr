%default total

bug : (n, m : Nat) -> n + m = n -> Void
bug _ _ Refl impossible

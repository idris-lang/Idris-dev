module tbad

total
bad : Nat -> Nat
bad Z = Z
bad (S m) with (succ m)
    bad _ | j = bad j


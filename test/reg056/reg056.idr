k : (a : Type) -> (x, y : a) -> (p, q : x = y) -> p = q
k a x x Refl Refl = Refl

postulate trap : Z = Z

dodgy : (a, b : ()) -> a = b -> Void
dodgy n m Refl impossible

nonk : (trap = Refl {Z}) -> Void
nonk Refl impossible

false : Void
false = nonk (k Nat Z Z trap Refl)



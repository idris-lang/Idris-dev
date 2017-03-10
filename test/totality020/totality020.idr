%default total

bug : (n, m : Nat) -> n + m = n -> Void
bug _ _ Refl impossible

foo : (a : Bool) -> (b : Bool) -> Not (const a b = b)
foo a b Refl impossible

myVoid : Void
myVoid = foo True True Refl


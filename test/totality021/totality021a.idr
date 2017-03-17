%default total

-- Testing that overloaded names are properly spotted in impossible cases
data Point : Nat -> t -> Type where
  Nil : Point Z t
  (::) : Num t => t -> Point n t -> Point (S n) t

noNonEmptyPointInt : (Point (S n) Int) -> Void
noNonEmptyPointInt {n} Nil impossible

myVoid : Void
myVoid = noNonEmptyPointInt [2]

import Data.Vect

total
finZEmpty : Fin Z -> a

fins : (n : Nat) -> (xs : Vect n (Fin n) ** ((x : Fin n) -> Elem x xs))
fins Z     = ([] ** (finZEmpty {a=_}))

-- f : (a : Nat) -> a = S a -> _|_
-- f a = believe_me


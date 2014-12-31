import Data.Vect
import Data.Fin

total
finZEmpty : Fin Z -> a

fins : (n : Nat) -> (xs : Vect n (Fin n) ** ((x : Fin n) -> Elem x xs))
fins Z     = ([] ** (finZEmpty {a=_}))

-- f : (a : Nat) -> a = S a -> Void
-- f a = believe_me


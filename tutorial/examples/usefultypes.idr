
intVec : Vect Int 5
intVec = [1, 2, 3, 4, 5]

double : Int -> Int
double x = x * 2

vec : (n ** Vect Int n)
vec = (_ ** [3, 4])

list_lookup : Nat -> List a -> Maybe a
list_lookup _     Nil         = Nothing
list_lookup O     (x :: xs) = Just x
list_lookup (S k) (x :: xs) = list_lookup k xs

lookup_default : Nat -> List a -> a -> a
lookup_default i xs def = case list_lookup i xs of
                              Nothing => def
                            | Just x => x


import Data.Vect

total
vassoc : (xs : Vect n a) -> (ys : Vect m a) -> (zs : Vect p a) ->
         xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
vassoc [] ys zs = Refl
vassoc (x :: xs) ys zs 
    = rewrite vassoc xs ys zs in Refl
total
vassoc' : (xs : Vect n a) -> (ys : Vect m a) -> (zs : Vect p a) ->
         xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
vassoc' [] ys zs = Refl
vassoc' (x :: xs) ys zs 
    = rewrite vassoc xs ys xs in Refl

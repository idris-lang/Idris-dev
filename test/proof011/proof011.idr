import Data.Vect

vreplace : {xs : Vect n a} -> {ys : Vect m a} ->
           (P : {len : Nat} -> Vect len a -> Type) ->
           xs = ys -> P ys -> P xs
vreplace P Refl prop = prop

total
vassoc : (xs : Vect n a) -> (ys : Vect m a) -> (zs : Vect p a) ->
         xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
vassoc [] ys zs = Refl
vassoc (x :: xs) ys zs 
    = rewrite vassoc xs ys zs using vreplace in 
              Refl
total
vassoc' : (xs : Vect n a) -> (ys : Vect m a) -> (zs : Vect p a) ->
         xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
vassoc' [] ys zs = Refl
vassoc' (x :: xs) ys zs 
    = rewrite vassoc xs ys xs using vreplace in 
              Refl

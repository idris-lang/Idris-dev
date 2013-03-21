vfoldl : (P : Nat -> Type) -> 
         ((x : Nat) -> P x -> a -> P (S x)) -> P O
       -> Vect a m -> P m
-- vfoldl P cons nil []        
--     = nil
vfoldl P cons nil (x :: xs) 
    = vfoldl (\n => P (S n)) (\ n => cons (S n)) (cons O nil x) xs
%logging 0
-- vfoldl P cons nil (x :: xs) 
--     = vfoldl (\n => P (S n)) (\ n => cons _) (cons _ nil x) xs

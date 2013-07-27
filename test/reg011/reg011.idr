vfoldl : (P : Nat -> Type) -> 
         ((x : Nat) -> P x -> a -> P (S x)) -> P Z
       -> Vect m a -> P m
-- vfoldl P cons nil []        
--     = nil
vfoldl P cons nil (x :: xs) 
    = vfoldl (\k => P (S k)) (\ n => cons (S n)) (cons Z nil x) xs
-- vfoldl P cons nil (x :: xs) 
--     = vfoldl (\n => P (S n)) (\ n => cons _) (cons _ nil x) xs

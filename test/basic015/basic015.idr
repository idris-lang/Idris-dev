{-
data Nat = Z | S Nat

plus : Nat -> Nat -> Nat
plus Z y = y
plus (S x) y = S (plus x y)
-}

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

append : Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys


zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f [] ys = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

create_empties : Vect m (Vect 0 elem)
create_empties {m = Z} = []
create_empties {m = (S k)} = [] :: create_empties

transpose_helper : (row : Vect m elem) -> (rest_trans : Vect m (Vect k elem)) ->
                   Vect m (Vect (S k) elem)
transpose_helper [] [] = []
transpose_helper (rowval :: xs) (restrow :: ys) = (rowval :: restrow) :: transpose_helper xs ys

transpose_vec : Vect n (Vect m elem) -> Vect m (Vect n elem)
transpose_vec [] = create_empties
transpose_vec (row :: rest) = let rest_trans = transpose_vec rest in
                                  transpose_helper row rest_trans








------- A main program to read dimensions, generate and tranpose a vector

implementation Functor (Vect m) where
    map m [] = []
    map m (x :: xs) = m x :: map m xs

implementation Show a => Show (Vect m a) where
    show x = show (toList x)
      where
        toList : Vect m a -> List a
        toList [] = []
        toList (y :: xs) = y :: toList xs

countTo : (m : Nat) -> Vect m Int
countTo Z = []
countTo (S k) = 0 :: map (+1) (countTo k)

mkVect : (n, m : Nat) -> Vect n (Vect m Int)
mkVect Z m = []
mkVect (S k) m = countTo m :: map (map (+ cast m)) (mkVect k m)

main : IO ()
main = do putStr "Rows: "
          let r : Nat = 5 
          putStr "Columns: "
          let c : Nat = 6 
          printLn (mkVect r c)
          putStrLn "Transposed:"
          printLn (transpose_vec (mkVect r c))

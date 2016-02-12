||| Basic matrix operations with dimensionalities enforced
||| at the type level
module Data.Matrix

import public Data.Vect

%default total
%access public export

||| Matrix with n rows and m columns
Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)

||| Get the specified column of a matrix
getCol : Fin m -> Matrix n m a -> Vect n a
getCol f = map (index f)

||| Get the specified row of a matrix
getRow : Fin n -> Matrix n m a -> Vect m a
getRow = index

||| Delete the specified column of a matrix
deleteCol : Fin (S m) -> Matrix n (S m) a -> Matrix n m a
deleteCol f = map (deleteAt f)

||| Delete the specified row of a matrix
deleteRow : Fin (S n) -> Matrix (S n) m a -> Matrix n m a
deleteRow = deleteAt

insertRow : Fin (S n) -> Vect m a -> Matrix n m a -> Matrix (S n) m a
insertRow = insertAt

insertCol : Fin (S m) -> Vect n a -> Matrix n m a -> Matrix n (S m) a
insertCol f = zipWith (insertAt f)

||| Matrix element at specified row and column indices
indices : Fin n -> Fin m -> Matrix n m a -> a
indices f1 f2 = index f2 . index f1

||| Cast a vector from a standard Vect to a proper n x 1 matrix
col : Vect n a -> Matrix n 1 a
col = map (\x => [x])

||| Cast a row from a standard Vect to a proper 1 x n matrix
row : Vect n a -> Matrix 1 n a
row r = [r]

||| Matrix formed by deleting specified row and col
subMatrix : Fin (S n) -> Fin (S m) -> Matrix (S n) (S m) a -> Matrix n m a
subMatrix r c = deleteRow r . deleteCol c

||| Flatten a matrix of matrices
concatMatrix : Matrix n m (Matrix x y a) -> Matrix (n * x) (m * y) a
concatMatrix = Vect.concat . map (map Vect.concat) . map transpose

||| All finite numbers of the specified level
fins : (n : Nat) -> Vect n (Fin n)
fins Z     = Nil
fins (S n) = FZ :: (map FS $ fins n)

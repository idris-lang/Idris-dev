import Data.Vect

impTy : Bool -> Type
impTy True = Int
impTy False = {n : Nat} -> Vect n Int -> Vect n Int

wibble : impTy False
wibble [] = [] 
wibble (x :: xs) = x * 2 :: wibble xs

wobble : (b : Bool) -> impTy b
wobble True = 42
wobble False = wibble

foo : Vect 4 Int
foo = wobble False [1,2,3,4]

bar : Int
bar = wobble True

module Main

import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality

Cell : Nat -> Type
Cell n = Maybe (Fin n)

data Board : Nat -> Type where
  MkBoard : {n : Nat} -> Vect n (Vect n (Cell n)) -> Board n

emptyBoard : {n : Nat} -> Board n
emptyBoard {n=n} = MkBoard (replicate n (replicate n Nothing))

Empty : Cell n -> Type
Empty {n=n} x = (the (Cell n) Nothing) = x

Filled : Cell n -> Type
Filled {n=n} = (\x => Not (Empty x))

FullBoard : Board n -> Type
FullBoard (MkBoard b) = All (All Filled) b

indexStep : {i : Fin n} -> {xs : Vect n a} -> {x : a} -> index i xs = index (FS i) (x::xs)
indexStep = Refl

find : {p : a -> Type} -> ((x : a) -> Dec (p x)) -> (xs : Vect n a)
       -> Either (All (\x => Not (p x)) xs) (y : a ** (p y, (i : Fin n ** y = index i xs)))
find _ Nil = Left Nil
find {p} d (x::xs) with (d x)
  | Yes prf = Right (x ** (prf, (FZ ** Refl)))
  | No prf =
    case find {p} d xs of
      Right (y ** (prf', (i ** prf''))) =>
        Right (y ** (prf', (FS i ** replace {P=(\x => y = x)} (indexStep {x=x}) prf'')))
      Left prf' => Left (prf::prf')

empty : (cell : Cell n) -> Dec (Empty cell)
empty Nothing = Yes Refl
empty (Just _) = No nothingNotJust

findEmptyInRow : (xs : Vect n (Cell n)) -> Either (All Filled xs) (i : Fin n ** Empty (index i xs))
findEmptyInRow xs =
  case find {p=Empty} empty xs of
    Right (_ ** (pempty, (i ** pidx))) => Right (i ** trans pempty pidx)
    Left p => Left p

getCell : Board n -> (Fin n, Fin n) -> Cell n
getCell (MkBoard b) (x, y) = index x (index y b)

emptyCell : {n : Nat} -> (b : Board n) -> 
         Either (FullBoard b) (c : (Fin n, Fin n) ** Empty (getCell b c))
emptyCell (MkBoard rs) = 
  case helper rs of
    Left p => Left p
    Right (ri ** (ci ** pf2)) => Right ((ci, ri) ** pf2)
 where
  helper : (rs : Vect m (Vect n (Cell n)))
           -> Either (All (All Filled) rs) (r : Fin m ** (c : Fin n ** Empty (index c (index r rs))))
  helper Nil = Left Nil
  helper (r::rs) =
    case findEmptyInRow r of
      Right (ci ** pf3) => Right (FZ ** (ci ** pf3))
      Left prf =>
        case helper rs of
          Left prf' => Left (prf::prf')
          Right (ri ** (ci ** pf4)) => Right (FS ri ** (ci ** pf4))


main : IO ()
main =
  case emptyCell (emptyBoard {n=0}) of
    Left _ => putStrLn "l"
    Right _ => putStrLn "r"


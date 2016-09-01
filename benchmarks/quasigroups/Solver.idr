module Solver

import Decidable.Equality
import Control.Monad.State
import Data.Vect
import Data.Vect.Quantifiers

%default total
%access public export

Cell : Nat -> Type
Cell n = Maybe (Fin n)

data Board : Nat -> Type where
  MkBoard : {n : Nat} -> Vect n (Vect n (Cell n)) -> Board n

emptyBoard : Board n
emptyBoard {n=n} = MkBoard (replicate n (replicate n Nothing))

showElt : Cell n -> String
showElt Nothing = "."
showElt (Just x) = show (1 + (the Int (fromInteger (cast x))))

-- FIXME: Inline type decl should not be necessary here
showRow : Vect n (Cell n) -> String
showRow {n=n} xs = unwords (toList (the (Vect n String) (map showElt xs)))

unlines : Vect n String -> String
unlines Nil = ""
unlines (l::Nil) = l
unlines (l::ls) = pack (foldl addLine (unpack l) (map unpack ls))
  where
    addLine : List Char -> List Char -> List Char
    addLine w s = w ++ ('\n' :: s)

Show (Board n) where
  show (MkBoard rs) = unlines (map showRow rs)

updateAt : Fin n -> Vect n a -> (a -> a) -> Vect n a
updateAt FZ (x::xs) f = f x :: xs
updateAt (FS i) (x::xs) f = x :: updateAt i xs f

setCell : Board n -> (Fin n, Fin n) -> Fin n -> Board n
setCell (MkBoard b) (x, y) value = MkBoard (updateAt y b (\row => updateAt x row (const (Just value))))

getCell : Board n -> (Fin n, Fin n) -> Cell n
getCell (MkBoard b) (x, y) = index x (index y b)

anyElim : {xs : Vect n a} -> {P : a -> Type} -> (Any P xs -> b) -> (P x -> b) -> Any P (x :: xs) -> b
anyElim _ f (Here p) = f p
anyElim f _ (There p) = f p

getRow : Fin n -> Board n -> Vect n (Cell n)
getRow i (MkBoard b) = index i b

getCol : Fin n -> Board n -> Vect n (Cell n)
getCol i (MkBoard b) = helper i b
  where
    helper : Fin n -> Vect m (Vect n a) -> Vect m a
    helper _ Nil = Nil
    helper i (xs::xss) = index i xs :: helper i xss

LegalNeighbors : Cell n -> Cell n -> Type
LegalNeighbors (Just x) (Just y) = Not (x = y)
LegalNeighbors _ _ = ()

legalNeighbors : (x : Cell n) -> (y : Cell n) -> Dec (LegalNeighbors x y)
legalNeighbors (Just x) (Just y) with (decEq x y)
  | Yes prf = No (\pf => pf prf)
  | No prf = Yes prf
legalNeighbors Nothing (Just _) = Yes ()
legalNeighbors (Just _) Nothing = Yes ()
legalNeighbors Nothing Nothing = Yes ()

rowSafe : (b : Board n) -> (r : Fin n) -> (val : Fin n) -> Dec (All (LegalNeighbors (Just val)) (getRow r b))
rowSafe b r v = all (legalNeighbors (Just v)) (getRow r b)

colSafe : (b : Board n) -> (r : Fin n) -> (val : Fin n) -> Dec (All (LegalNeighbors (Just val)) (getCol r b))
colSafe b r v = all (legalNeighbors (Just v)) (getCol r b)

Empty : Cell n -> Type
Empty {n=n} x = (the (Cell n) Nothing) = x

empty : (cell : Cell n) -> Dec (Empty cell)
empty Nothing = Yes Refl
empty (Just _) = No nothingNotJust

-- Predicate for legal cell assignments
LegalVal : Board n -> (Fin n, Fin n) -> Fin n -> Type
LegalVal b (x, y) val = (Empty (getCell b (x, y)), All (LegalNeighbors (Just val)) (getCol x b), All (LegalNeighbors (Just val)) (getRow y b))

legalVal : (b : Board n) -> (coord : (Fin n, Fin n)) -> (val : Fin n) -> Dec (LegalVal b coord val)
legalVal b (x, y) v =
  case rowSafe b y v of
    No prf => No (\(_, _, rf) => prf rf)
    Yes prf =>
      case colSafe b x v of
        No prf' => No (\(_, cf, _) => prf' cf)
        Yes prf' =>
          case Solver.empty (getCell b (x, y)) of
            No prf'' => No (\(ef, _, _) => prf'' ef)
            Yes prf'' => Yes (prf'', prf', prf)


Filled : Cell n -> Type
--Filled {n=n} x = Not (Empty x) -- TODO: Find out why this doesn't work
Filled {n=n} = (\x => Not (Empty x))
--Filled {n=n} x = the (Maybe (Fin n)) Nothing = x -> Void
--Filled {n=n} = \x => the (Maybe (Fin n)) Nothing = x -> Void

filled : (cell : Cell n) -> Dec (Filled cell)
filled Nothing = No (\f => f Refl)
filled (Just _) = Yes nothingNotJust

FullBoard : Board n -> Type
FullBoard (MkBoard b) = All (All Filled) b

fullBoard : (b : Board n) -> Dec (FullBoard b)
fullBoard (MkBoard b) = all (all filled) b

fins : Vect n (Fin n)
fins {n=Z} = Nil
fins {n=(S m)} = last :: map weaken fins

data LegalBoard : Board n -> Type where
  Base : LegalBoard (emptyBoard {n})
  Step : {b : Board n} -> {coords : (Fin n, Fin n)} -> {v : Fin n} -> LegalVal b coords v -> LegalBoard b -> LegalBoard (setCell b coords v)

CompleteBoard : Board n -> Type
CompleteBoard b = (LegalBoard b, FullBoard b)

indexStep : {i : Fin n} -> {xs : Vect n a} -> {x : a} -> index i xs = index (FS i) (x::xs)
indexStep = Refl

find : {P : a -> Type} -> ((x : a) -> Dec (P x)) -> (xs : Vect n a)
       -> Either (All (\x => Not (P x)) xs) (y : a ** (P y, (i : Fin n ** y = index i xs)))
find _ Nil = Left Nil
find d (x::xs) with (d x)
  | Yes prf = Right (x ** (prf, (FZ ** Refl)))
  | No prf =
    case find d xs of
      Right (y ** (prf', (i ** prf''))) =>
        Right (y ** (prf', (FS i ** replace {P=(\x => y = x)} (indexStep {x=x}) prf'')))
      Left prf' => Left (prf::prf')

findEmptyInRow : (xs : Vect n (Cell n)) -> Either (All Filled xs) (i : Fin n ** Empty (index i xs))
findEmptyInRow xs =
  case find {P=Empty} empty xs of
    Right (_ ** (pempty, (i ** pidx))) => Right (i ** trans pempty pidx)
    Left p => Left p

emptyCell : (b : Board n) -> Either (FullBoard b) (c : (Fin n, Fin n) ** Empty (getCell b c))
emptyCell (MkBoard rs) =
  case helper rs of
    Left p => Left p
    Right (ri ** (ci ** pf)) => Right ((ci, ri) ** pf)
  where
    helper : (rs : Vect m (Vect n (Cell n)))
             -> Either (All (All Filled) rs) (r : Fin m ** (c : Fin n ** Empty (index c (index r rs))))
    helper Nil = Left Nil
    helper (r::rs) =
      case findEmptyInRow r of
        Right (ci ** pf) => Right (FZ ** (ci ** pf))
        Left prf =>
          case helper rs of
            Left prf' => Left (prf::prf')
            Right (ri ** (ci ** pf)) => Right (FS ri ** (ci ** pf))


tryValue : {b : Board (S n)} -> LegalBoard b -> (c : (Fin (S n), Fin (S n))) -> Empty (getCell b c) -> (v : Fin (S n))
           -> Either (Not (LegalVal b c v)) (b' : Board (S n) ** LegalBoard b')
tryValue {b=b} l c _ v =
  case legalVal b c v of
    No prf => Left prf
    Yes prf => Right (_ ** Step prf l)

nullBoardFull : (b : Board Z) -> FullBoard b
nullBoardFull (MkBoard Nil) = Nil

-- TODO: Prove complete by induction on illegal values wrt. some base state, e.g. every value is illegal for 123\21_\3_2
fillBoard : (b : Board n) -> LegalBoard b -> Maybe (b' : Board n ** CompleteBoard b')
fillBoard {n=Z} b l = Just (b ** (l, nullBoardFull b))
fillBoard {n=(S n)} b l with (emptyCell b)
  | Left full = Just (b ** (l, full))
  | Right (coords ** p) = recurse last
  where
    tryAll : (v : Fin (S n)) -> (Fin (S n), Maybe (b' : Board (S n) ** LegalBoard b'))
    tryAll v = assert_total $ --trace ("Trying " ++ show (the Int (cast v))) $
      case tryValue l coords p v of
        Right success => (v, Just success)
        Left _ => -- TODO: Prove unsolvable
          case v of
            FS k => tryAll (weaken k)
            FZ => (v, Nothing)

    recurse : Fin (S n) -> Maybe (b' : Board (S n) ** CompleteBoard b')
    recurse start = assert_total $
      case tryAll start of
        (_, Nothing) => Nothing
        (FZ, Just (b' ** l')) => fillBoard b' l'
        (FS next, Just (b' ** l')) =>
          case fillBoard b' l' of
            Just solution => Just solution
            Nothing => recurse (weaken next)

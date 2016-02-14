||| Types for interfacing with C.
||| This file should be kept free from IO.
module CFFI.Types

import Data.Vect
import Data.HVect

%access public export
%default partial

||| An universe of C types.
data CType = I8 | I16 | I32 | I64 | FLOAT | DOUBLE | PTR

data Composite = T CType | ARRAY Int Composite | STRUCT (List Composite) | UNION (List Composite)
                | PACKEDSTRUCT (List Composite)

implicit mkComposite : CType -> Composite
mkComposite x = T x

Show CType where
    show I8 = "I8"
    show I16 = "I16"
    show I32 = "I32"
    show I64 = "I64"
    show FLOAT = "FLOAT"
    show DOUBLE = "DOUBLE"
    show PTR = "PTR"

Show Composite where
    show (T ct) = show ct
    show (ARRAY n t) = "ARRAY " ++ show n ++ " " ++ show t
    show (STRUCT xs) = "STRUCT " ++ show xs
    show (UNION xs) = "UNION " ++ show xs
    show (PACKEDSTRUCT xs) = "PACKEDSTRUCT " ++ show xs

translate : CType -> Type
translate I8 = Bits8
translate I16 = Bits16
translate I32 = Bits32
translate I64 = Bits64
translate FLOAT = Double
translate DOUBLE = Double
translate PTR = Ptr

translateComp : Composite -> Type
translateComp (T ct) = translate ct
translateComp  (ARRAY n t) = Vect (toNat n) (translateComp t)
translateComp  (STRUCT xs) = HVect $ fromList (map translateComp xs)
translateComp  (UNION xs) = HVect $ fromList (map translateComp xs)
translateComp  (PACKEDSTRUCT xs) = HVect $ fromList (map translateComp xs)

mutual
    sizeOf : CType -> Int
    sizeOf I8 = 1
    sizeOf I16 = 2
    sizeOf I32 = 4
    sizeOf I64 = 8
    sizeOf FLOAT = 4
    sizeOf DOUBLE = 8
    sizeOf PTR = prim__sizeofPtr

    sizeOfComp : Composite -> Int
    sizeOfComp (T ct) = sizeOf ct
    sizeOfComp (ARRAY n t) = n * sizeOfComp t
    sizeOfComp (STRUCT xs) = sizeOfStruct xs
    sizeOfComp (UNION xs) = foldl (\acc, x =>max acc $ sizeOfComp x) 0 xs
    sizeOfComp (PACKEDSTRUCT xs) = foldl (\acc, x => acc + sizeOfComp x) 0 xs

    alignOf : CType -> Int
    alignOf I8 = 1
    alignOf I16 = 2
    alignOf I32 = 4
    alignOf I64 = prim__sizeofPtr
    alignOf FLOAT = 4
    alignOf DOUBLE = prim__sizeofPtr
    alignOf PTR = prim__sizeofPtr

    alignOfComp : Composite -> Int
    alignOfComp (T t) = alignOf t
    alignOfComp (ARRAY n t) = alignOfComp t
    alignOfComp (STRUCT xs) = foldl (\acc, x => max acc $ alignOfComp x) 0 xs
    alignOfComp (UNION xs) = foldl (\acc, x => max acc $ alignOfComp x) 0 xs
    alignOfComp (PACKEDSTRUCT xs) = 1

    offsetsStruct : List Composite -> List Int
    offsetsStruct xs = offsets' xs [] 0
        where
            offsets' : List Composite -> List Int -> Int -> List Int
            offsets' [] acc _ = reverse acc
            offsets' (x::xs) ys curr = let a = alignOfComp x
                                           padding = let c = curr `mod` a
                                                        in if c == 0 then 0 else a - c
                                           off = curr + padding
                                       in offsets' xs (off::ys) (off + sizeOfComp x)

    sizeOfStruct : List Composite -> Int
    sizeOfStruct xs = case (reverse xs, reverse (offsetsStruct xs)) of
                        ([], _) => 0
                        (x::_, y::_) => let end = y + sizeOfComp x
                                            endPadding = let c = end `mod` align in
                                                if c == 0 then 0 else align - c
                                        in end + endPadding
        where
            align : Int
            align = foldl (\acc, x => max acc $ alignOfComp x) 1 xs

fields : Composite -> Nat
fields (STRUCT xs) = length xs
fields (PACKEDSTRUCT xs) = length xs
fields (UNION xs) = length xs
fields (ARRAY n _) = toNat n
fields _ = 1

offsetsPacked : List Composite -> List Int
offsetsPacked xs = offsets' xs [] 0
    where
        offsets' : List Composite -> List Int -> Int -> List Int
        offsets' [] acc _ = reverse acc
        offsets' (x::xs) acc pos = offsets' xs (pos::acc) (sizeOfComp x)

-- TODO: Use index and fix upp proofs.
offset : Composite -> Nat -> Int
offset (STRUCT xs) i = fromMaybe 0 $ index' i (offsetsStruct xs)
offset (PACKEDSTRUCT xs) i = fromMaybe 0 $ index' i (offsetsPacked xs)
offset (ARRAY _ t) i = sizeOfComp t * toIntNat i
offset _ _ = 0

offsets : Composite -> List Int
offsets (STRUCT xs) = offsetsStruct xs
offsets (PACKEDSTRUCT xs) = offsetsPacked xs
offsets (UNION xs) = replicate (length xs) 0
offsets (ARRAY n t) = [ x*sizeOfComp t | x <- [0..n-1]]
offsets _ = [0]

-- TODO: handle out of bounds with proofs
-- Also choose a better name.
select : Composite -> Nat -> Composite
select (STRUCT xs@(y::_)) i = fromMaybe y (index' i xs)
select (PACKEDSTRUCT xs@(y::_)) i = fromMaybe y (index' i xs)
select (UNION xs@(y::_)) i = fromMaybe y (index' i xs)
select (ARRAY n t) _ = t
select t _ = t

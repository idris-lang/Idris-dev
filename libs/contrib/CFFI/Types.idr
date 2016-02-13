||| Types for interfacing with C.
module CFFI.Types

import Data.Vect
import Data.HList

%access public export
%default partial

||| An universe of C types.
data CType = I8 | I16 | I32 | I64 | FLOAT | DOUBLE | PTR
            | ARRAY Int CType | STRUCT (List CType) | UNION (List CType)
            | PACKEDSTRUCT (List CType)

translate : CType -> Type
translate I8 = Bits8
translate I16 = Bits16
translate I32 = Bits32
translate I64 = Bits64
translate FLOAT = Double
translate DOUBLE = Double
translate PTR = Ptr
translate (ARRAY n t) = Vect (toNat n) (translate t)
translate (STRUCT xs) = HList (map translate xs)
translate (UNION xs) = HList (map translate xs)
translate (PACKEDSTRUCT xs) = HList (map translate xs)

mutual
    sizeOf : CType -> Int
    sizeOf I8 = 1
    sizeOf I16 = 2
    sizeOf I32 = 4
    sizeOf I64 = 8
    sizeOf FLOAT = 4
    sizeOf DOUBLE = 8
    sizeOf PTR = prim__sizeofPtr
    sizeOf (ARRAY n t) = n * sizeOf t
    sizeOf (STRUCT xs) = sizeOfStruct xs
    sizeOf (UNION xs) = foldl (\acc, x =>max acc $ sizeOf x) 0 xs
    sizeOf (PACKEDSTRUCT xs) = foldl (\acc, x => acc + sizeOf x) 0 xs

    alignOf : CType -> Int
    alignOf I8 = 1
    alignOf I16 = 2
    alignOf I32 = 4
    alignOf I64 = prim__sizeofPtr
    alignOf FLOAT = 4
    alignOf DOUBLE = prim__sizeofPtr
    alignOf PTR = prim__sizeofPtr
    alignOf (ARRAY n t) = alignOf t
    alignOf (STRUCT xs) = foldl (\acc, x => max acc $ alignOf x) 0 xs
    alignOf (UNION xs) = foldl (\acc, x => max acc $ alignOf x) 0 xs
    alignOf (PACKEDSTRUCT xs) = 1

    offsetsStruct : List CType -> List Int
    offsetsStruct xs = offsets' xs [] 0
        where
            offsets' : List CType -> List Int -> Int -> List Int
            offsets' [] acc _ = reverse acc
            offsets' (x::xs) ys curr = let a = alignOf x
                                           padding = let c = curr `mod` a
                                                        in if c == 0 then 0 else a - c
                                           off = curr + padding
                                       in offsets' xs (off::ys) (off + sizeOf x)

    sizeOfStruct : List CType -> Int
    sizeOfStruct xs = case (reverse xs, reverse (offsetsStruct xs)) of
                        ([], _) => 0
                        (x::_, y::_) => let end = y + sizeOf x
                                            endPadding = let c = end `mod` align in
                                                if c == 0 then 0 else align - c
                                        in end + endPadding
        where
            align : Int
            align = foldl (\acc, x => max acc $ alignOf x) 1 xs

fields : CType -> Nat
fields (STRUCT xs) = length xs
fields (PACKEDSTRUCT xs) = length xs
fields (UNION xs) = length xs
fields (ARRAY n _) = toNat n
fields _ = 1

offsetsPacked : List CType -> List Int
offsetsPacked xs = offsets' xs [] 0
    where
        offsets' : List CType -> List Int -> Int -> List Int
        offsets' [] acc _ = reverse acc
        offsets' (x::xs) acc pos = offsets' xs (pos::acc) (sizeOf x)

-- TODO: Use index and fix upp proofs.
offset : CType -> Nat -> Int
offset (STRUCT xs) i = fromMaybe 0 $ index' i (offsetsStruct xs)
offset (PACKEDSTRUCT xs) i = fromMaybe 0 $ index' i (offsetsPacked xs)
offset (ARRAY _ t) i = sizeOf t * toIntNat i
offset _ _ = 0

offsets : CType -> List Int
offsets (STRUCT xs) = offsetsStruct xs
offsets (PACKEDSTRUCT xs) = offsetsPacked xs
offsets (UNION xs) = replicate (length xs) 0
offsets (ARRAY n t) = [ x*sizeOf t | x <- [0..n]]
offsets _ = [0]

-- TODO: handle out of bounds with proofs
select : CType -> Nat -> CType
select (STRUCT xs@(y::_)) i = fromMaybe y (index' i xs)
select (PACKEDSTRUCT xs@(y::_)) i = fromMaybe y (index' i xs)
select (UNION xs@(y::_)) i = fromMaybe y (index' i xs)
select (ARRAY n t) _ = t
select t _ = t

module Bits

%default total

log2ceil : Nat -> Nat
log2ceil n = let x = log2 n in
             if x == log2 (n-1)
             then x+1
             else x

Bits : Nat -> Type
Bits x with (log2ceil x)
  | (S (S (S (S (S (S _)))))) = Bits64
  | (S (S (S (S (S O))))) = Bits32
  | (S (S (S (S O)))) = Bits16
  | _ = Bits8

intToBits : {n: Nat} -> Int -> Bits n
intToBits {n=n} x with (Bits n)
    | Bits8 = prim__intToB8 x
    | Bits16 = prim__intToB16 x
    | Bits32 = prim__intToB32 x
    | Bits64 = prim__intToB64 x

bitsAdd : {n : Nat} -> Bits n -> Bits n -> Bits n
bitsAdd {n=m} x y with (Bits m)
    | Bits8 = prim__addB8 x y
    | Bits16 = prim__addB16 x y
    | Bits32 = prim__addB32 x y
    | Bits64 = prim__addB64 x y

bitsSub : {n : Nat} -> Bits n -> Bits n -> Bits n
bitsSub {n=m} x y with (Bits m)
    | Bits8 = prim__subB8 x y
    | Bits16 = prim__subB16 x y
    | Bits32 = prim__subB32 x y
    | Bits64 = prim__subB64 x y

bitsMul : {n : Nat} -> Bits n -> Bits n -> Bits n
bitsMul {n=m} x y with (Bits m)
    | Bits8 = prim__mulB8 x y
    | Bits16 = prim__mulB16 x y
    | Bits32 = prim__mulB32 x y
    | Bits64 = prim__mulB64 x y

bitsSDiv : {n : Nat} -> Bits n -> Bits n -> Bits n
bitsSDiv {n=m} x y with (Bits m)
    | Bits8 = prim__sdivB8 x y
    | Bits16 = prim__sdivB16 x y
    | Bits32 = prim__sdivB32 x y
    | Bits64 = prim__sdivB64 x y

bitsUDiv : {n : Nat} -> Bits n -> Bits n -> Bits n
bitsUDiv {n=m} x y with (Bits m)
    | Bits8 = prim__udivB8 x y
    | Bits16 = prim__udivB16 x y
    | Bits32 = prim__udivB32 x y
    | Bits64 = prim__udivB64 x y

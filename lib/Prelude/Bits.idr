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

bitsShl : {n: Nat} -> Bits n -> Bits n -> Bits n
bitsShl {n=n} x c with (Bits n)
    | Bits8 = prim__shlB8 x c
    | Bits16 = prim__shlB16 x c
    | Bits32 = prim__shlB32 x c
    | Bits64 = prim__shlB64 x c

bitsLShr : {n: Nat} -> Bits n -> Bits n -> Bits n
bitsLShr {n=n} x c with (Bits n)
    | Bits8 = prim__lshrB8 x c
    | Bits16 = prim__lshrB16 x c
    | Bits32 = prim__lshrB32 x c
    | Bits64 = prim__lshrB64 x c

bitsAShr : {n: Nat} -> Bits n -> Bits n -> Bits n
bitsAShr {n=n} x c with (Bits n)
    | Bits8 = prim__ashrB8 x c
    | Bits16 = prim__ashrB16 x c
    | Bits32 = prim__ashrB32 x c
    | Bits64 = prim__ashrB64 x c

bitsAnd : {n: Nat} -> Bits n -> Bits n -> Bits n
bitsAnd {n=n} x y with (Bits n)
    | Bits8 = prim__andB8 x y
    | Bits16 = prim__andB16 x y
    | Bits32 = prim__andB32 x y
    | Bits64 = prim__andB64 x y

bitsOr : {n: Nat} -> Bits n -> Bits n -> Bits n
bitsOr {n=n} x y with (Bits n)
    | Bits8 = prim__orB8 x y
    | Bits16 = prim__orB16 x y
    | Bits32 = prim__orB32 x y
    | Bits64 = prim__orB64 x y

bitsXOr : {n: Nat} -> Bits n -> Bits n -> Bits n
bitsXOr {n=n} x y with (Bits n)
    | Bits8 = prim__xorB8 x y
    | Bits16 = prim__xorB16 x y
    | Bits32 = prim__xorB32 x y
    | Bits64 = prim__xorB64 x y

bitsAdd : {n : Nat} -> Bits n -> Bits n -> Bits n
bitsAdd {n=n} x y with (Bits n)
    | Bits8 = prim__addB8 x y
    | Bits16 = prim__addB16 x y
    | Bits32 = prim__addB32 x y
    | Bits64 = prim__addB64 x y

bitsSub : {n : Nat} -> Bits n -> Bits n -> Bits n
bitsSub {n=n} x y with (Bits n)
    | Bits8 = prim__subB8 x y
    | Bits16 = prim__subB16 x y
    | Bits32 = prim__subB32 x y
    | Bits64 = prim__subB64 x y

bitsMul : {n : Nat} -> Bits n -> Bits n -> Bits n
bitsMul {n=n} x y with (Bits n)
    | Bits8 = prim__mulB8 x y
    | Bits16 = prim__mulB16 x y
    | Bits32 = prim__mulB32 x y
    | Bits64 = prim__mulB64 x y

bitsSDiv : {n : Nat} -> Bits n -> Bits n -> Bits n
bitsSDiv {n=n} x y with (Bits n)
    | Bits8 = prim__sdivB8 x y
    | Bits16 = prim__sdivB16 x y
    | Bits32 = prim__sdivB32 x y
    | Bits64 = prim__sdivB64 x y

bitsUDiv : {n : Nat} -> Bits n -> Bits n -> Bits n
bitsUDiv {n=n} x y with (Bits n)
    | Bits8 = prim__udivB8 x y
    | Bits16 = prim__udivB16 x y
    | Bits32 = prim__udivB32 x y
    | Bits64 = prim__udivB64 x y

bitsToStr : {n : Nat} -> Bits n -> String
bitsToStr {n=n} x with (Bits n)
    | Bits8 = prim__b8ToStr x
    | Bits16 = prim__b16ToStr x
    | Bits32 = prim__b32ToStr x
    | Bits64 = prim__b64ToStr x

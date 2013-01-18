module Prelude.Bits

import Prelude.Strings

%default total

log2ceil : Nat -> Nat
log2ceil n = let x = log2 n in
             if x == log2 (n-1)
             then x+1
             else x

log2Bytes : Nat -> Nat
log2Bytes bits = (log2ceil (bits `div` 8))

machineTy : Nat -> Type
machineTy O = Bits8
machineTy (S O) = Bits16
machineTy (S (S O)) = Bits32
machineTy (S (S (S _))) = Bits64

public
data Bits : Nat -> Type where
    MkBits : machineTy (log2Bytes n) -> Bits n

pad8 : Nat -> (Bits8 -> Bits8 -> Bits8) -> Bits8 -> Bits8 -> Bits8
pad8 n f x y = prim__lshrB8 (f (prim__shlB8 x pad) (prim__shlB8 y pad)) pad
    where
      pad = (prim__intToB8 (cast (8-n)))

pad16 : Nat -> (Bits16 -> Bits16 -> Bits16) -> Bits16 -> Bits16 -> Bits16
pad16 n f x y = prim__lshrB16 (f (prim__shlB16 x pad) (prim__shlB16 y pad)) pad
    where
      pad = (prim__intToB16 (cast (16-n)))

pad32 : Nat -> (Bits32 -> Bits32 -> Bits32) -> Bits32 -> Bits32 -> Bits32
pad32 n f x y = prim__lshrB32 (f (prim__shlB32 x pad) (prim__shlB32 y pad)) pad
    where
      pad = (prim__intToB32 (cast (32-n)))

pad64 : Nat -> (Bits64 -> Bits64 -> Bits64) -> Bits64 -> Bits64 -> Bits64
pad64 n f x y = prim__lshrB64 (f (prim__shlB64 x pad) (prim__shlB64 y pad)) pad
    where
      pad = (prim__intToB64 (cast (64-n)))

-- These versions only pad the first operand
pad8' : Nat -> (Bits8 -> Bits8 -> Bits8) -> Bits8 -> Bits8 -> Bits8
pad8' n f x y = prim__lshrB8 (f (prim__shlB8 x pad) y) pad
    where
      pad = (prim__intToB8 (cast (8-n)))

pad16' : Nat -> (Bits16 -> Bits16 -> Bits16) -> Bits16 -> Bits16 -> Bits16
pad16' n f x y = prim__lshrB16 (f (prim__shlB16 x pad) y) pad
    where
      pad = (prim__intToB16 (cast (16-n)))

pad32' : Nat -> (Bits32 -> Bits32 -> Bits32) -> Bits32 -> Bits32 -> Bits32
pad32' n f x y = prim__lshrB32 (f (prim__shlB32 x pad) y) pad
    where
      pad = (prim__intToB32 (cast (32-n)))

pad64' : Nat -> (Bits64 -> Bits64 -> Bits64) -> Bits64 -> Bits64 -> Bits64
pad64' n f x y = prim__lshrB64 (f (prim__shlB64 x pad) y) pad
    where
      pad = (prim__intToB64 (cast (64-n)))

%assert_total
pow : Int -> Int -> Int
pow x y = if y > 0
          then x * (pow x (y - 1))
          else 1

%assert_total
intToBits' : Int -> machineTy (log2Bytes n)
intToBits' {n=n} x with (log2Bytes n)
    | O = let pad = (prim__intToB8 (cast (8-n))) in
          prim__lshrB8 (prim__shlB8 (prim__intToB8 x) pad) pad
    | S O = let pad = (prim__intToB16 (cast (16-n))) in
            prim__lshrB16 (prim__shlB16 (prim__intToB16 x) pad) pad
    | S (S O) = let pad = (prim__intToB32 (cast (32-n))) in
                prim__lshrB32 (prim__shlB32 (prim__intToB32 x) pad) pad
    | S (S (S _)) = let pad = (prim__intToB64 (cast (64-n))) in
                    prim__lshrB64 (prim__shlB64 (prim__intToB64 x) pad) pad

public
intToBits : Int -> Bits n
intToBits n = MkBits (intToBits' n)

instance Cast Int (Bits n) where
    cast = intToBits

unsafeBitsToInt' : machineTy n -> Int
unsafeBitsToInt' {n=n} x with n
    | O = prim__B32ToInt (prim__zextB8_32 x)
    | S O = prim__B32ToInt (prim__zextB16_32 x)
    | S (S O) = prim__B32ToInt x
    | S (S (S _)) = prim__B32ToInt (prim__truncB64_32 x)

public
unsafeBitsToInt : Bits n -> Int
unsafeBitsToInt (MkBits x) = unsafeBitsToInt' x

bitsShl' : machineTy (log2Bytes n) -> machineTy (log2Bytes n) -> machineTy (log2Bytes n)
bitsShl' {n=n} x c with (log2Bytes n)
    | O = pad8' n prim__shlB8 x c
    | S O = pad16' n prim__shlB16 x c
    | S (S O) = pad32' n prim__shlB32 x c
    | S (S (S _)) = pad64' n prim__shlB64 x c

public
bitsShl : Bits n -> Bits n -> Bits n
bitsShl (MkBits x) (MkBits y) = MkBits (bitsShl' x y)

bitsLShr' : machineTy n -> machineTy n -> machineTy n
bitsLShr' {n=n} x c with n
    | O = prim__lshrB8 x c
    | S O = prim__lshrB16 x c
    | S (S O) = prim__lshrB32 x c
    | S (S (S _)) = prim__lshrB64 x c

public
bitsLShr : Bits n -> Bits n -> Bits n
bitsLShr (MkBits x) (MkBits y) = MkBits (bitsLShr' x y)

bitsAShr' : machineTy (log2Bytes n) -> machineTy (log2Bytes n) -> machineTy (log2Bytes n)
bitsAShr' {n=n} x c with (log2Bytes n)
    | O = pad8' n prim__ashrB8 x c
    | S O = pad16' n prim__ashrB16 x c
    | S (S O) = pad32' n prim__ashrB32 x c
    | S (S (S _)) = pad64' n prim__ashrB64 x c

public
bitsAShr : Bits n -> Bits n -> Bits n
bitsAShr (MkBits x) (MkBits y) = MkBits (bitsAShr' x y)

bitsAnd' : machineTy n -> machineTy n -> machineTy n
bitsAnd' {n=n} x y with n
    | O = prim__andB8 x y
    | S O = prim__andB16 x y
    | S (S O) = prim__andB32 x y
    | S (S (S _)) = prim__andB64 x y

public
bitsAnd : Bits n -> Bits n -> Bits n
bitsAnd (MkBits x) (MkBits y) = MkBits (bitsAnd' x y)

bitsOr' : machineTy n -> machineTy n -> machineTy n
bitsOr' {n=n} x y with n
    | O = prim__orB8 x y
    | S O = prim__orB16 x y
    | S (S O) = prim__orB32 x y
    | S (S (S _)) = prim__orB64 x y

public
bitsOr : Bits n -> Bits n -> Bits n
bitsOr (MkBits x) (MkBits y) = MkBits (bitsOr' x y)

bitsXOr' : machineTy n -> machineTy n -> machineTy n
bitsXOr' {n=n} x y with n
    | O = prim__xorB8 x y
    | S O = prim__xorB16 x y
    | S (S O) = prim__xorB32 x y
    | S (S (S _)) = prim__xorB64 x y

public
bitsXOr : Bits n -> Bits n -> Bits n
bitsXOr (MkBits x) (MkBits y) = MkBits (bitsXOr' x y)

bitsAdd' : machineTy (log2Bytes n) -> machineTy (log2Bytes n) -> machineTy (log2Bytes n)
bitsAdd' {n=n} x y with (log2Bytes n)
    | O = pad8 n prim__addB8 x y
    | S O = pad16 n prim__addB16 x y
    | S (S O) = pad32 n prim__addB32 x y
    | S (S (S _)) = pad64 n prim__addB64 x y

public
bitsAdd : Bits n -> Bits n -> Bits n
bitsAdd (MkBits x) (MkBits y) = MkBits (bitsAdd' x y)

bitsSub' : machineTy (log2Bytes n) -> machineTy (log2Bytes n) -> machineTy (log2Bytes n)
bitsSub' {n=n} x y with (log2Bytes n)
    | O = pad8 n prim__subB8 x y
    | S O = pad16 n prim__subB16 x y
    | S (S O) = pad32 n prim__subB32 x y
    | S (S (S _)) = pad64 n prim__subB64 x y

public
bitsSub : Bits n -> Bits n -> Bits n
bitsSub (MkBits x) (MkBits y) = MkBits (bitsSub' x y)

bitsMul' : machineTy (log2Bytes n) -> machineTy (log2Bytes n) -> machineTy (log2Bytes n)
bitsMul' {n=n} x y with (log2Bytes n)
    | O = pad8 n prim__mulB8 x y
    | S O = pad16 n prim__mulB16 x y
    | S (S O) = pad32 n prim__mulB32 x y
    | S (S (S _)) = pad64 n prim__mulB64 x y

public
bitsMul : Bits n -> Bits n -> Bits n
bitsMul (MkBits x) (MkBits y) = MkBits (bitsMul' x y)

partial
bitsSDiv' : machineTy (log2Bytes n) -> machineTy (log2Bytes n) -> machineTy (log2Bytes n)
bitsSDiv' {n=n} x y with (log2Bytes n)
    | O = prim__sdivB8 x y
    | S O = prim__sdivB16 x y
    | S (S O) = prim__sdivB32 x y
    | S (S (S _)) = prim__sdivB64 x y

public partial
bitsSDiv : Bits n -> Bits n -> Bits n
bitsSDiv (MkBits x) (MkBits y) = MkBits (bitsSDiv' x y)

partial
bitsUDiv' : machineTy (log2Bytes n) -> machineTy (log2Bytes n) -> machineTy (log2Bytes n)
bitsUDiv' {n=n} x y with (log2Bytes n)
    | O = prim__udivB8 x y
    | S O = prim__udivB16 x y
    | S (S O) = prim__udivB32 x y
    | S (S (S _)) = prim__udivB64 x y

public partial
bitsUDiv : Bits n -> Bits n -> Bits n
bitsUDiv (MkBits x) (MkBits y) = MkBits (bitsUDiv' x y)

partial
bitsSRem' : machineTy (log2Bytes n) -> machineTy (log2Bytes n) -> machineTy (log2Bytes n)
bitsSRem' {n=n} x y with (log2Bytes n)
    | O = prim__sremB8 x y
    | S O = prim__sremB16 x y
    | S (S O) = prim__sremB32 x y
    | S (S (S _)) = prim__sremB64 x y

public partial
bitsSRem : Bits n -> Bits n -> Bits n
bitsSRem (MkBits x) (MkBits y) = MkBits (bitsSRem' x y)

partial
bitsURem' : machineTy (log2Bytes n) -> machineTy (log2Bytes n) -> machineTy (log2Bytes n)
bitsURem' {n=n} x y with (log2Bytes n)
    | O = prim__uremB8 x y
    | S O = prim__uremB16 x y
    | S (S O) = prim__uremB32 x y
    | S (S (S _)) = prim__uremB64 x y

public partial
bitsURem : Bits n -> Bits n -> Bits n
bitsURem (MkBits x) (MkBits y) = MkBits (bitsURem' x y)

-- TODO: Proofy comparisons via postulates
bitsLt' : machineTy n -> machineTy n -> Int
bitsLt' {n=n} x y with n
    | O = prim__ltB8 x y
    | S O = prim__ltB16 x y
    | S (S O) = prim__ltB32 x y
    | S (S (S _)) = prim__ltB64 x y

public
bitsLt : Bits n -> Bits n -> Bool
bitsLt (MkBits x) (MkBits y) = bitsLt' x y /= 0

bitsLte' : machineTy n -> machineTy n -> Int
bitsLte' {n=n} x y with n
    | O = prim__lteB8 x y
    | S O = prim__lteB16 x y
    | S (S O) = prim__lteB32 x y
    | S (S (S _)) = prim__lteB64 x y

public
bitsLte : Bits n -> Bits n -> Bool
bitsLte (MkBits x) (MkBits y) = bitsLte' x y /= 0

bitsEq' : machineTy n -> machineTy n -> Int
bitsEq' {n=n} x y with n
    | O = prim__eqB8 x y
    | S O = prim__eqB16 x y
    | S (S O) = prim__eqB32 x y
    | S (S (S _)) = prim__eqB64 x y

public
bitsEq : Bits n -> Bits n -> Bool
bitsEq (MkBits x) (MkBits y) = bitsEq' x y /= 0

bitsGte' : machineTy n -> machineTy n -> Int
bitsGte' {n=n} x y with n
    | O = prim__gteB8 x y
    | S O = prim__gteB16 x y
    | S (S O) = prim__gteB32 x y
    | S (S (S _)) = prim__gteB64 x y

public
bitsGte : Bits n -> Bits n -> Bool
bitsGte (MkBits x) (MkBits y) = bitsGte' x y /= 0

bitsGt' : machineTy n -> machineTy n -> Int
bitsGt' {n=n} x y with n
    | O = prim__gtB8 x y
    | S O = prim__gtB16 x y
    | S (S O) = prim__gtB32 x y
    | S (S (S _)) = prim__gtB64 x y

public
bitsGt : Bits n -> Bits n -> Bool
bitsGt (MkBits x) (MkBits y) = bitsGt' x y /= 0

instance Eq (Bits n) where
    (==) = bitsEq

instance Ord (Bits n) where
    (<) = bitsLt
    (<=) = bitsLte
    (>=) = bitsGte
    (>) = bitsGt
    compare x y = if x `bitsLt` y
                  then LT
                  else if x `bitsEq` y
                       then EQ
                       else GT

complement' : machineTy n -> machineTy n
complement' {n=n} x with n
    | O = prim__complB8 x
    | S O = prim__complB16 x
    | S (S O) = prim__complB32 x
    | S (S (S _)) = prim__complB64 x

public
complement : Bits n -> Bits n
complement (MkBits x) = MkBits (complement' x)

public
bitSet : Fin n -> Bits n -> Bool
bitSet n x = bitsAnd (intToBits 1 `bitsShl` intToBits (cast (finToNat n))) x /= intToBits 0

public
bitsToStr : Bits n -> String
bitsToStr x = pack (helper last x)
    where
      %assert_total
      helper : Fin (S n) -> Bits n -> List Char
      helper fO _ = []
      helper (fS x) b = (if bitSet x b then '1' else '0') :: helper (weaken x) b

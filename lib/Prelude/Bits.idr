module Prelude.Bits

import Prelude.Strings

%default total

divCeil : Nat -> Nat -> Nat
divCeil x y = case x `mod` y of
                O   => x `div` y
                S _ => S (x `div` y)

nextPow2 : Nat -> Nat
nextPow2 O = O
nextPow2 x = if x == (2 `power` l2x)
             then l2x
             else S l2x
    where
      l2x = log2 x

nextBytes : Nat -> Nat
nextBytes bits = (nextPow2 (bits `divCeil` 8))

machineTy : Nat -> Type
machineTy O = Bits8
machineTy (S O) = Bits16
machineTy (S (S O)) = Bits32
machineTy (S (S (S _))) = Bits64

public
data Bits : Nat -> Type where
    MkBits : machineTy (nextBytes n) -> Bits n

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
intToBits' : Int -> machineTy (nextBytes n)
intToBits' {n=n} x with (nextBytes n)
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

bitsToInt' : machineTy n -> Int
bitsToInt' {n=n} x with n
    | O = prim__B32ToInt (prim__zextB8_32 x)
    | S O = prim__B32ToInt (prim__zextB16_32 x)
    | S (S O) = prim__B32ToInt x
    | S (S (S _)) = prim__B32ToInt (prim__truncB64_32 x)

public
bitsToInt : Bits n -> Int
bitsToInt (MkBits x) = bitsToInt' x

shiftLeft' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
shiftLeft' {n=n} x c with (nextBytes n)
    | O = pad8' n prim__shlB8 x c
    | S O = pad16' n prim__shlB16 x c
    | S (S O) = pad32' n prim__shlB32 x c
    | S (S (S _)) = pad64' n prim__shlB64 x c

public
shiftLeft : Bits n -> Bits n -> Bits n
shiftLeft (MkBits x) (MkBits y) = MkBits (shiftLeft' x y)

shiftRightLogical' : machineTy n -> machineTy n -> machineTy n
shiftRightLogical' {n=n} x c with n
    | O = prim__lshrB8 x c
    | S O = prim__lshrB16 x c
    | S (S O) = prim__lshrB32 x c
    | S (S (S _)) = prim__lshrB64 x c

public
shiftRightLogical : Bits n -> Bits n -> Bits n
shiftRightLogical (MkBits x) (MkBits y) = MkBits (shiftRightLogical' x y)

shiftRightArithmetic' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
shiftRightArithmetic' {n=n} x c with (nextBytes n)
    | O = pad8' n prim__ashrB8 x c
    | S O = pad16' n prim__ashrB16 x c
    | S (S O) = pad32' n prim__ashrB32 x c
    | S (S (S _)) = pad64' n prim__ashrB64 x c

public
shiftRightArithmetic : Bits n -> Bits n -> Bits n
shiftRightArithmetic (MkBits x) (MkBits y) = MkBits (shiftRightArithmetic' x y)

and' : machineTy n -> machineTy n -> machineTy n
and' {n=n} x y with n
    | O = prim__andB8 x y
    | S O = prim__andB16 x y
    | S (S O) = prim__andB32 x y
    | S (S (S _)) = prim__andB64 x y

public
and : Bits n -> Bits n -> Bits n
and (MkBits x) (MkBits y) = MkBits (and' x y)

or' : machineTy n -> machineTy n -> machineTy n
or' {n=n} x y with n
    | O = prim__orB8 x y
    | S O = prim__orB16 x y
    | S (S O) = prim__orB32 x y
    | S (S (S _)) = prim__orB64 x y

public
or : Bits n -> Bits n -> Bits n
or (MkBits x) (MkBits y) = MkBits (or' x y)

xor' : machineTy n -> machineTy n -> machineTy n
xor' {n=n} x y with n
    | O = prim__xorB8 x y
    | S O = prim__xorB16 x y
    | S (S O) = prim__xorB32 x y
    | S (S (S _)) = prim__xorB64 x y

public
xor : Bits n -> Bits n -> Bits n
xor (MkBits x) (MkBits y) = MkBits (xor' x y)

plus' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
plus' {n=n} x y with (nextBytes n)
    | O = pad8 n prim__addB8 x y
    | S O = pad16 n prim__addB16 x y
    | S (S O) = pad32 n prim__addB32 x y
    | S (S (S _)) = pad64 n prim__addB64 x y

public
plus : Bits n -> Bits n -> Bits n
plus (MkBits x) (MkBits y) = MkBits (plus' x y)

minus' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
minus' {n=n} x y with (nextBytes n)
    | O = pad8 n prim__subB8 x y
    | S O = pad16 n prim__subB16 x y
    | S (S O) = pad32 n prim__subB32 x y
    | S (S (S _)) = pad64 n prim__subB64 x y

public
minus : Bits n -> Bits n -> Bits n
minus (MkBits x) (MkBits y) = MkBits (minus' x y)

times' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
times' {n=n} x y with (nextBytes n)
    | O = pad8 n prim__mulB8 x y
    | S O = pad16 n prim__mulB16 x y
    | S (S O) = pad32 n prim__mulB32 x y
    | S (S (S _)) = pad64 n prim__mulB64 x y

public
times : Bits n -> Bits n -> Bits n
times (MkBits x) (MkBits y) = MkBits (times' x y)

partial
sdiv' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
sdiv' {n=n} x y with (nextBytes n)
    | O = prim__sdivB8 x y
    | S O = prim__sdivB16 x y
    | S (S O) = prim__sdivB32 x y
    | S (S (S _)) = prim__sdivB64 x y

public partial
sdiv : Bits n -> Bits n -> Bits n
sdiv (MkBits x) (MkBits y) = MkBits (sdiv' x y)

partial
udiv' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
udiv' {n=n} x y with (nextBytes n)
    | O = prim__udivB8 x y
    | S O = prim__udivB16 x y
    | S (S O) = prim__udivB32 x y
    | S (S (S _)) = prim__udivB64 x y

public partial
udiv : Bits n -> Bits n -> Bits n
udiv (MkBits x) (MkBits y) = MkBits (udiv' x y)

partial
srem' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
srem' {n=n} x y with (nextBytes n)
    | O = prim__sremB8 x y
    | S O = prim__sremB16 x y
    | S (S O) = prim__sremB32 x y
    | S (S (S _)) = prim__sremB64 x y

public partial
srem : Bits n -> Bits n -> Bits n
srem (MkBits x) (MkBits y) = MkBits (srem' x y)

partial
urem' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
urem' {n=n} x y with (nextBytes n)
    | O = prim__uremB8 x y
    | S O = prim__uremB16 x y
    | S (S O) = prim__uremB32 x y
    | S (S (S _)) = prim__uremB64 x y

public partial
urem : Bits n -> Bits n -> Bits n
urem (MkBits x) (MkBits y) = MkBits (urem' x y)

-- TODO: Proofy comparisons via postulates
lt : machineTy n -> machineTy n -> Int
lt {n=n} x y with n
    | O = prim__ltB8 x y
    | S O = prim__ltB16 x y
    | S (S O) = prim__ltB32 x y
    | S (S (S _)) = prim__ltB64 x y

lte : machineTy n -> machineTy n -> Int
lte {n=n} x y with n
    | O = prim__lteB8 x y
    | S O = prim__lteB16 x y
    | S (S O) = prim__lteB32 x y
    | S (S (S _)) = prim__lteB64 x y

eq : machineTy n -> machineTy n -> Int
eq {n=n} x y with n
    | O = prim__eqB8 x y
    | S O = prim__eqB16 x y
    | S (S O) = prim__eqB32 x y
    | S (S (S _)) = prim__eqB64 x y

gte : machineTy n -> machineTy n -> Int
gte {n=n} x y with n
    | O = prim__gteB8 x y
    | S O = prim__gteB16 x y
    | S (S O) = prim__gteB32 x y
    | S (S (S _)) = prim__gteB64 x y

gt : machineTy n -> machineTy n -> Int
gt {n=n} x y with n
    | O = prim__gtB8 x y
    | S O = prim__gtB16 x y
    | S (S O) = prim__gtB32 x y
    | S (S (S _)) = prim__gtB64 x y

instance Eq (Bits n) where
    (MkBits x) == (MkBits y) = boolOp eq x y

instance Ord (Bits n) where
    (MkBits x) < (MkBits y) = boolOp lt x y
    (MkBits x) <= (MkBits y) = boolOp lte x y
    (MkBits x) >= (MkBits y) = boolOp gte x y
    (MkBits x) > (MkBits y) = boolOp gt x y
    compare (MkBits x) (MkBits y) =
        if (x `lt` y) /= 0
        then LT
        else if (x `eq` y) /= 0
             then EQ
             else GT

complement' : machineTy (nextBytes n) -> machineTy (nextBytes n)
complement' {n=n} x with (nextBytes n)
    | O = let pad = prim__intToB8 (8 - cast n) in
          prim__complB8 (x `prim__shlB8` pad) `prim__lshrB8` pad
    | S O = let pad = prim__intToB16 (16 - cast n) in
            prim__complB16 (x `prim__shlB16` pad) `prim__lshrB16` pad
    | S (S O) = let pad = prim__intToB32 (32 - cast n) in
                prim__complB32 (x `prim__shlB32` pad) `prim__lshrB32` pad
    | S (S (S _)) = let pad = prim__intToB64 (64 - cast n) in
                    prim__complB64 (x `prim__shlB64` pad) `prim__lshrB64` pad

public
complement : Bits n -> Bits n
complement (MkBits x) = MkBits (complement' x)

-- TODO: Prove
%assert_total
zext' : machineTy (nextBytes n) -> machineTy (nextBytes (n+m))
zext' {n=n} {m=m} x with (nextBytes n, nextBytes (n+m))
    | (O, O) = believe_me x
    | (O, S O) = believe_me (prim__zextB8_16 (believe_me x))
    | (O, S (S O)) = believe_me (prim__zextB8_32 (believe_me x))
    | (O, S (S (S _))) = believe_me (prim__zextB8_64 (believe_me x))
    | (S O, S O) = believe_me x
    | (S O, S (S O)) = believe_me (prim__zextB16_32 (believe_me x))
    | (S O, S (S (S _))) = believe_me (prim__zextB16_64 (believe_me x))
    | (S (S O), S (S O)) = believe_me x
    | (S (S O), S (S (S _))) = believe_me (prim__zextB32_64 (believe_me x))
    | (S (S (S _)), S (S (S _))) = believe_me x

public partial
zeroExtend : Bits n -> Bits (n+m)
zeroExtend (MkBits x) = MkBits (zext' x)

-- Fill in the high bits of a sign-extended bitstring
fixupSE : (m : Nat) -> machineTy (nextBytes (n+m)) -> machineTy (nextBytes (n+m))
fixupSE m x = x `or'` complement' (zext' {m=m} (complement' (intToBits' 0)))

-- TODO: Prove
%assert_total
sext' : machineTy (nextBytes n) -> machineTy (nextBytes (n+m))
sext' {n=n} {m=m} x with (nextBytes n, nextBytes (n+m))
    | (O, O) = fixupSE m (believe_me x)
    | (O, S O) = fixupSE m (believe_me (prim__sextB8_16 (believe_me x)))
    | (O, S (S O)) = fixupSE m (believe_me (prim__sextB8_32 (believe_me x)))
    | (O, S (S (S _))) = fixupSE m (believe_me (prim__sextB8_64 (believe_me x)))
    | (S O, S O) = fixupSE m (believe_me x)
    | (S O, S (S O)) = fixupSE m (believe_me (prim__sextB16_32 (believe_me x)))
    | (S O, S (S (S _))) = fixupSE m (believe_me (prim__sextB16_64 (believe_me x)))
    | (S (S O), S (S O)) = fixupSE m (believe_me x)
    | (S (S O), S (S (S _))) = fixupSE m (believe_me (prim__sextB32_64 (believe_me x)))
    | (S (S (S _)), S (S (S _))) = fixupSE m (believe_me x)

public partial
signExtend : Bits n -> Bits (n+m)
signExtend (MkBits x) = MkBits (sext' x)

-- Zero out the high bits of a truncated bitstring
fixupTR : machineTy (nextBytes n) -> machineTy (nextBytes n)
fixupTR x = x `and'` complement' (intToBits' 0)

-- TODO: Prove
%assert_total
trunc' : machineTy (nextBytes (n+m)) -> machineTy (nextBytes n)
trunc' {n=n} {m=m} x with (nextBytes n, nextBytes (n+m))
    | (O, O) = fixupTR (believe_me x)
    | (O, S O) = believe_me (prim__truncB16_8 (believe_me x))
    | (O, S (S O)) = believe_me (prim__truncB32_8 (believe_me x))
    | (O, S (S (S _))) = believe_me (prim__truncB64_8 (believe_me x))
    | (S O, S O) = fixupTR (believe_me x)
    | (S O, S (S O)) = believe_me (prim__truncB32_16 (believe_me x))
    | (S O, S (S (S _))) = believe_me (prim__truncB64_16 (believe_me x))
    | (S (S O), S (S O)) = fixupTR (believe_me x)
    | (S (S O), S (S (S _))) = believe_me (prim__truncB64_32 (believe_me x))
    | (S (S (S _)), S (S (S _))) = fixupTR (believe_me x)

public partial
truncate : Bits (n+m) -> Bits n
truncate (MkBits x) = MkBits (trunc' x)

bitAt : Fin n -> Bits n
bitAt n = intToBits 1 `shiftLeft` intToBits (cast n)

public
getBit : Fin n -> Bits n -> Bool
getBit n x = (x `and` (bitAt n)) /= intToBits 0

public
setBit : Fin n -> Bits n -> Bits n
setBit n x = x `or` (bitAt n)

public
unsetBit : Fin n -> Bits n -> Bits n
unsetBit n x = x `and` complement (bitAt n)

public
bitsToStr : Bits n -> String
bitsToStr x = pack (helper last x)
    where
      %assert_total
      helper : Fin (S n) -> Bits n -> List Char
      helper fO _ = []
      helper (fS x) b = (if getBit x b then '1' else '0') :: helper (weaken x) b

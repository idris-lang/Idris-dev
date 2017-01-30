module Data.Bits

import Data.Fin

%default total -- This file is full of totality assertions though. Let's try
               -- to improve it! (EB)
%access export

||| Finds the next exponent of a power of two.
||| For example `nextPow2 200 = 8`, because 2^8 = 256.
||| If it is an exact match, it is not rounded up: `nextPow2 256 = 8` because 2^8 = 256.
public export
nextPow2 : Nat -> Nat
nextPow2 Z = Z
nextPow2 (S x) = if (S x) == (2 `power` l2x)
               then l2x
               else S l2x
    where
      l2x = log2NZ (S x) SIsNotZ

||| Gets the lowest n for which "8 * 2 ^ n" is larger than or equal to the input.
||| For example, `nextBytes 10 = 16`.
||| Like with nextPow2, the result is not rounded up, so `nextBytes 16 = 16`.
public export
nextBytes : Nat -> Nat
nextBytes bits = (nextPow2 (divCeilNZ bits 8 SIsNotZ))

||| An index function to access the Bits* types in order.
||| machineTy 0 = Bits8, machineTy 1 = Bits16, etc.
||| Any input that would result in getting a type that is larger than supported
||| will result in the largest supported type instead (currently 64 bits).
public export
machineTy : Nat -> Type
machineTy Z = Bits8
machineTy (S Z) = Bits16
machineTy (S (S Z)) = Bits32
machineTy (S (S (S _))) = Bits64

||| Finds the number of bits used by `machineTy n`.
||| For example, bitsUsed 2 = 16
bitsUsed : Nat -> Nat
bitsUsed n = 8 * (2 `power` n)

||| Converts a Nat to a machineTy n, with the first argument as an accumulator.
||| You shouldn't have to call this manually, use natToBits (without ') instead.
natToBits' : %static {n : Nat} -> machineTy n -> Nat -> machineTy n
natToBits' a Z = a
natToBits' {n=n} a x with (n)
 -- it seems I have to manually recover the value of n here, instead of being able to reference it
 natToBits' a (S x') | Z           = natToBits' {n=0} (prim__addB8  a (prim__truncInt_B8  1)) x'
 natToBits' a (S x') | S Z         = natToBits' {n=1} (prim__addB16 a (prim__truncInt_B16 1)) x'
 natToBits' a (S x') | S (S Z)     = natToBits' {n=2} (prim__addB32 a (prim__truncInt_B32 1)) x'
 natToBits' a (S x') | S (S (S _)) = natToBits' {n=3} (prim__addB64 a (prim__truncInt_B64 1)) x'
 natToBits' a _      | _           = assert_unreachable

||| Converts a Nat to a machineTy n.
natToBits : %static {n : Nat} -> Nat -> machineTy n
natToBits {n=n} x with (n)
    | Z           = natToBits' {n=0} (prim__truncInt_B8  0) x
    | S Z         = natToBits' {n=1} (prim__truncInt_B16 0) x
    | S (S Z)     = natToBits' {n=2} (prim__truncInt_B32 0) x
    | S (S (S _)) = natToBits' {n=3} (prim__truncInt_B64 0) x
    | _           = assert_unreachable

getPad : %static {n : Nat} -> Nat -> machineTy n
getPad n = assert_total $ natToBits (minus (bitsUsed (nextBytes n)) n)

||| A "high-level" wrapper to the types defined by `machineTy`.
public export
data Bits : Nat -> Type where
    ||| An bits type that has at least n bits available,
    ||| up to the maximum supported by `machineTy`.
    MkBits : machineTy (nextBytes n) -> Bits n

||| Perform a function over Bits8 as if it is carried out on n bits.
||| (n should be 8 or lower)
pad8 : (n : Nat) -> (Bits8 -> Bits8 -> Bits8) -> Bits8 -> Bits8 -> Bits8
pad8 n f x y = prim__lshrB8 (f (prim__shlB8 x pad) (prim__shlB8 y pad)) pad
    where
      pad = getPad {n=0} n

||| Perform a function over Bits16 as if it is carried out on n bits.
||| (n should be 16 or lower)
pad16 : (n: Nat) -> (Bits16 -> Bits16 -> Bits16) -> Bits16 -> Bits16 -> Bits16
pad16 n f x y = prim__lshrB16 (f (prim__shlB16 x pad) (prim__shlB16 y pad)) pad
    where
      pad = getPad {n=1} n

||| Perform a function over Bits32 as if it is carried out on n bits.
||| (n should be 32 or lower)
pad32 : Nat -> (Bits32 -> Bits32 -> Bits32) -> Bits32 -> Bits32 -> Bits32
pad32 n f x y = prim__lshrB32 (f (prim__shlB32 x pad) (prim__shlB32 y pad)) pad
    where
      pad = getPad {n=2} n

||| Perform a function over Bits64 as if it is carried out on n bits.
||| (n should be 64 or lower)
pad64 : Nat -> (Bits64 -> Bits64 -> Bits64) -> Bits64 -> Bits64 -> Bits64
pad64 n f x y = prim__lshrB64 (f (prim__shlB64 x pad) (prim__shlB64 y pad)) pad
    where
      pad = getPad {n=3} n

-- These versions only pad the first operand
pad8' : Nat -> (Bits8 -> Bits8 -> Bits8) -> Bits8 -> Bits8 -> Bits8
pad8' n f x y = prim__lshrB8 (f (prim__shlB8 x pad) y) pad
    where
      pad = getPad {n=0} n

pad16' : Nat -> (Bits16 -> Bits16 -> Bits16) -> Bits16 -> Bits16 -> Bits16
pad16' n f x y = prim__lshrB16 (f (prim__shlB16 x pad) y) pad
    where
      pad = getPad {n=1} n

pad32' : Nat -> (Bits32 -> Bits32 -> Bits32) -> Bits32 -> Bits32 -> Bits32
pad32' n f x y = prim__lshrB32 (f (prim__shlB32 x pad) y) pad
    where
      pad = getPad {n=2} n

pad64' : Nat -> (Bits64 -> Bits64 -> Bits64) -> Bits64 -> Bits64 -> Bits64
pad64' n f x y = prim__lshrB64 (f (prim__shlB64 x pad) y) pad
    where
      pad = getPad {n=3} n

-- TODO: This (and all the other functions along these lines) is -- because it is used by things. Do they really need to be
-- public export, or is export good enough?
shiftLeft' : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
shiftLeft' {n=n} x c with (nextBytes n)
    | Z = pad8' n prim__shlB8 x c
    | S Z = pad16' n prim__shlB16 x c
    | S (S Z) = pad32' n prim__shlB32 x c
    | S (S (S _)) = pad64' n prim__shlB64 x c
    | _ = assert_unreachable

||| Binary left shift
shiftLeft : %static {n : Nat} -> Bits n -> Bits n -> Bits n
shiftLeft (MkBits x) (MkBits y) = MkBits (shiftLeft' x y)

||| Logical binary right shift
shiftRightLogical' : %static {n : Nat} -> machineTy n -> machineTy n -> machineTy n
shiftRightLogical' {n=n} x c with (n)
    | Z = prim__lshrB8 x c
    | S Z = prim__lshrB16 x c
    | S (S Z) = prim__lshrB32 x c
    | S (S (S _)) = prim__lshrB64 x c
    | _ = assert_unreachable

||| Logical binary right shift
shiftRightLogical : %static {n : Nat} -> Bits n -> Bits n -> Bits n
shiftRightLogical {n} (MkBits x) (MkBits y)
    = MkBits {n} (shiftRightLogical' {n=nextBytes n} x y)

||| Arithematic binary right shift
shiftRightArithmetic' : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
shiftRightArithmetic' {n=n} x c with (nextBytes n)
    | Z = pad8' n prim__ashrB8 x c
    | S Z = pad16' n prim__ashrB16 x c
    | S (S Z) = pad32' n prim__ashrB32 x c
    | S (S (S _)) = pad64' n prim__ashrB64 x c
    | _ = assert_unreachable

||| Arithematic binary right shift
shiftRightArithmetic : %static {n : Nat} -> Bits n -> Bits n -> Bits n
shiftRightArithmetic (MkBits x) (MkBits y) = MkBits (shiftRightArithmetic' x y)

||| Binary and
and' : %static {n : Nat} -> machineTy n -> machineTy n -> machineTy n
and' {n=n} x y with (n)
    | Z = prim__andB8 x y
    | S Z = prim__andB16 x y
    | S (S Z) = prim__andB32 x y
    | S (S (S _)) = prim__andB64 x y
    | _ = assert_unreachable

||| Binary and
and : %static {n : Nat} -> Bits n -> Bits n -> Bits n
and {n} (MkBits x) (MkBits y) = MkBits (and' {n=nextBytes n} x y)

||| Binary or
or' : %static {n : Nat} -> machineTy n -> machineTy n -> machineTy n
or' {n=n} x y with (n)
    | Z = prim__orB8 x y
    | S Z = prim__orB16 x y
    | S (S Z) = prim__orB32 x y
    | S (S (S _)) = prim__orB64 x y
    | _ = assert_unreachable

||| Binary or
or : %static {n : Nat} -> Bits n -> Bits n -> Bits n
or {n} (MkBits x) (MkBits y) = MkBits (or' {n=nextBytes n} x y)

||| Binary xor
xor' : %static {n : Nat} -> machineTy n -> machineTy n -> machineTy n
xor' {n=n} x y with (n)
    | Z = prim__xorB8 x y
    | S Z = prim__xorB16 x y
    | S (S Z) = prim__xorB32 x y
    | S (S (S _)) = prim__xorB64 x y
    | _ = assert_unreachable

||| Binary xor
xor : %static {n : Nat} -> Bits n -> Bits n -> Bits n
xor {n} (MkBits x) (MkBits y) = MkBits {n} (xor' {n=nextBytes n} x y)

||| Overflowing addition
plus' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
plus' {n=n} x y with (nextBytes n)
    | Z = pad8 n prim__addB8 x y
    | S Z = pad16 n prim__addB16 x y
    | S (S Z) = pad32 n prim__addB32 x y
    | S (S (S _)) = pad64 n prim__addB64 x y
    | _ = assert_unreachable

||| Overflowing addition
plus : %static {n : Nat} -> Bits n -> Bits n -> Bits n
plus (MkBits x) (MkBits y) = MkBits (plus' x y)

||| Subtraction
minus' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
minus' {n=n} x y with (nextBytes n)
    | Z = pad8 n prim__subB8 x y
    | S Z = pad16 n prim__subB16 x y
    | S (S Z) = pad32 n prim__subB32 x y
    | S (S (S _)) = pad64 n prim__subB64 x y
    | _ = assert_unreachable

||| Subtraction
minus : %static {n : Nat} -> Bits n -> Bits n -> Bits n
minus (MkBits x) (MkBits y) = MkBits (minus' x y)

||| Multiplication
times' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
times' {n=n} x y with (nextBytes n)
    | Z = pad8 n prim__mulB8 x y
    | S Z = pad16 n prim__mulB16 x y
    | S (S Z) = pad32 n prim__mulB32 x y
    | S (S (S _)) = pad64 n prim__mulB64 x y
    | _ = assert_unreachable

||| Multiplication
times : %static {n : Nat} -> Bits n -> Bits n -> Bits n
times (MkBits x) (MkBits y) = MkBits (times' x y)

||| Signed integer division
partial
sdiv' : machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
sdiv' {n=n} x y with (nextBytes n)
    | Z = prim__sdivB8 x y
    | S Z = prim__sdivB16 x y
    | S (S Z) = prim__sdivB32 x y
    | S (S (S _)) = prim__sdivB64 x y
    | _ = assert_unreachable

||| Signed integer division
partial
sdiv : %static {n : Nat} -> Bits n -> Bits n -> Bits n
sdiv (MkBits x) (MkBits y) = MkBits (sdiv' x y)

||| Unsigned integer division
partial
udiv' : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
udiv' {n=n} x y with (nextBytes n)
    | Z = prim__udivB8 x y
    | S Z = prim__udivB16 x y
    | S (S Z) = prim__udivB32 x y
    | S (S (S _)) = prim__udivB64 x y
    | _ = assert_unreachable

||| Unsigned integer division
partial
udiv : %static {n : Nat} -> Bits n -> Bits n -> Bits n
udiv (MkBits x) (MkBits y) = MkBits (udiv' x y)

||| Signed remainder (mod)
partial
srem' : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
srem' {n=n} x y with (nextBytes n)
    | Z = prim__sremB8 x y
    | S Z = prim__sremB16 x y
    | S (S Z) = prim__sremB32 x y
    | S (S (S _)) = prim__sremB64 x y
    | _ = assert_unreachable

||| Signed remainder (mod)
partial
srem : %static {n : Nat} -> Bits n -> Bits n -> Bits n
srem (MkBits x) (MkBits y) = MkBits (srem' x y)

||| Unsigned remainder (mod)
partial
urem' : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n) -> machineTy (nextBytes n)
urem' {n=n} x y with (nextBytes n)
    | Z = prim__uremB8 x y
    | S Z = prim__uremB16 x y
    | S (S Z) = prim__uremB32 x y
    | S (S (S _)) = prim__uremB64 x y
    | _ = assert_unreachable

||| Unsigned remainder (mod)
partial
urem : %static {n : Nat} -> Bits n -> Bits n -> Bits n
urem (MkBits x) (MkBits y) = MkBits (urem' x y)

-- TODO: Proofy comparisons via postulates
lt : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n) -> Int
lt {n=n} x y with (nextBytes n)
    | Z = prim__ltB8 x y
    | S Z = prim__ltB16 x y
    | S (S Z) = prim__ltB32 x y
    | S (S (S _)) = prim__ltB64 x y
    | _ = assert_unreachable

lte : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n) -> Int
lte {n=n} x y with (nextBytes n)
    | Z = prim__lteB8 x y
    | S Z = prim__lteB16 x y
    | S (S Z) = prim__lteB32 x y
    | S (S (S _)) = prim__lteB64 x y
    | _ = assert_unreachable

eq : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n) -> Int
eq {n=n} x y with (nextBytes n)
    | Z = prim__eqB8 x y
    | S Z = prim__eqB16 x y
    | S (S Z) = prim__eqB32 x y
    | S (S (S _)) = prim__eqB64 x y
    | _ = assert_unreachable

gte : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n) -> Int
gte {n=n} x y with (nextBytes n)
    | Z = prim__gteB8 x y
    | S Z = prim__gteB16 x y
    | S (S Z) = prim__gteB32 x y
    | S (S (S _)) = prim__gteB64 x y
    | _ = assert_unreachable

gt : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n) -> Int
gt {n=n} x y with (nextBytes n)
    | Z = prim__gtB8 x y
    | S Z = prim__gtB16 x y
    | S (S Z) = prim__gtB32 x y
    | S (S (S _)) = prim__gtB64 x y
    | _ = assert_unreachable

implementation Eq (Bits n) where
    (MkBits x) == (MkBits y) = boolOp eq x y

implementation Ord (Bits n) where
    (MkBits x) < (MkBits y) = boolOp lt x y
    (MkBits x) <= (MkBits y) = boolOp lte x y
    (MkBits x) >= (MkBits y) = boolOp gte x y
    (MkBits x) > (MkBits y) = boolOp gt x y
    compare (MkBits x) (MkBits y) =
        if boolOp lt x y
        then LT
        else if boolOp eq x y
             then EQ
             else GT

complement' : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n)
complement' {n=n} x with (nextBytes n)
    | Z = let pad = getPad {n=0} n in
          prim__complB8 (x `prim__shlB8` pad) `prim__lshrB8` pad
    | S Z = let pad = getPad {n=1} n in
            prim__complB16 (x `prim__shlB16` pad) `prim__lshrB16` pad
    | S (S Z) = let pad = getPad {n=2} n in
                prim__complB32 (x `prim__shlB32` pad) `prim__lshrB32` pad
    | S (S (S _)) = let pad = getPad {n=3} n in
                    prim__complB64 (x `prim__shlB64` pad) `prim__lshrB64` pad
    | _ = assert_unreachable

complement : %static {n : Nat} -> Bits n -> Bits n
complement (MkBits x) = MkBits (complement' x)

-- TODO: Prove
zext' : %static {n : Nat} -> %static {m : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes (n+m))
zext' {n=n} {m=m} x with (nextBytes n, nextBytes (n+m))
    | (Z, Z) = believe_me x
    | (Z, S Z) = believe_me (prim__zextB8_B16 (believe_me x))
    | (Z, S (S Z)) = believe_me (prim__zextB8_B32 (believe_me x))
    | (Z, S (S (S _))) = believe_me (prim__zextB8_B64 (believe_me x))
    | (S Z, S Z) = believe_me x
    | (S Z, S (S Z)) = believe_me (prim__zextB16_B32 (believe_me x))
    | (S Z, S (S (S _))) = believe_me (prim__zextB16_B64 (believe_me x))
    | (S (S Z), S (S Z)) = believe_me x
    | (S (S Z), S (S (S _))) = believe_me (prim__zextB32_B64 (believe_me x))
    | (S (S (S _)), S (S (S _))) = believe_me x
    | _ = assert_unreachable

zeroExtend : %static {n : Nat} -> %static {m : Nat} -> Bits n -> Bits (n+m)
zeroExtend (MkBits x) = MkBits (zext' x)

intToBits' : %static {n : Nat} -> Integer -> machineTy (nextBytes n)
intToBits' {n=n} x with (nextBytes n)
    | Z = let pad = getPad {n=0} n in
          prim__lshrB8 (prim__shlB8 (prim__truncBigInt_B8 x) pad) pad
    | S Z = let pad = getPad {n=1} n in
            prim__lshrB16 (prim__shlB16 (prim__truncBigInt_B16 x) pad) pad
    | S (S Z) = let pad = getPad {n=2} n in
                prim__lshrB32 (prim__shlB32 (prim__truncBigInt_B32 x) pad) pad
    | S (S (S _)) = let pad = getPad {n=3} n in
                    prim__lshrB64 (prim__shlB64 (prim__truncBigInt_B64 x) pad) pad
    | _ = assert_unreachable

intToBits : %static {n : Nat} -> Integer -> Bits n
intToBits n = MkBits (intToBits' n)

implementation Cast Integer (Bits n) where
    cast = intToBits

bitsToInt' : %static {n : Nat} -> machineTy (nextBytes n) -> Integer
bitsToInt' {n=n} x with (nextBytes n)
    | Z = prim__zextB8_BigInt x
    | S Z = prim__zextB16_BigInt x
    | S (S Z) = prim__zextB32_BigInt x
    | S (S (S _)) = prim__zextB64_BigInt x
    | _ = assert_unreachable

bitsToInt : %static {n : Nat} -> Bits n -> Integer
bitsToInt (MkBits x) = bitsToInt' x

-- Zero out the high bits of a truncated bitstring
zeroUnused : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes n)
zeroUnused {n} x = x `and'` complement' (intToBits' {n=n} 0)

--implementation Cast Nat (Bits n) where
--    cast x = MkBits (zeroUnused (natToBits n))

-- TODO: Prove
sext' : %static {n : Nat} -> machineTy (nextBytes n) -> machineTy (nextBytes (n+m))
sext' {n=n} {m=m} x with (nextBytes n, nextBytes (n+m))
    | (Z, Z) = let pad = getPad {n=0} n in
               believe_me (prim__ashrB8 (prim__shlB8 (believe_me x) pad) pad)
    | (Z, S Z) = let pad = getPad {n=0} n in
                 believe_me (prim__ashrB16 (prim__sextB8_B16 (prim__shlB8 (believe_me x) pad))
                                           (prim__zextB8_B16 pad))
    | (Z, S (S Z)) = let pad = getPad {n=0} n in
                     believe_me (prim__ashrB32 (prim__sextB8_B32 (prim__shlB8 (believe_me x) pad))
                                               (prim__zextB8_B32 pad))
    | (Z, S (S (S _))) = let pad = getPad {n=0} n in
                         believe_me (prim__ashrB64 (prim__sextB8_B64 (prim__shlB8 (believe_me x) pad))
                                                   (prim__zextB8_B64 pad))
    | (S Z, S Z) = let pad = getPad {n=1} n in
                   believe_me (prim__ashrB16 (prim__shlB16 (believe_me x) pad) pad)
    | (S Z, S (S Z)) = let pad = getPad {n=1} n in
                       believe_me (prim__ashrB32 (prim__sextB16_B32 (prim__shlB16 (believe_me x) pad))
                                                 (prim__zextB16_B32 pad))
    | (S Z, S (S (S _))) = let pad = getPad {n=1} n in
                           believe_me (prim__ashrB64 (prim__sextB16_B64 (prim__shlB16 (believe_me x) pad))
                                                     (prim__zextB16_B64 pad))
    | (S (S Z), S (S Z)) = let pad = getPad {n=2} n in
                           believe_me (prim__ashrB32 (prim__shlB32 (believe_me x) pad) pad)
    | (S (S Z), S (S (S _))) = let pad = getPad {n=2} n in
                               believe_me (prim__ashrB64 (prim__sextB32_B64 (prim__shlB32 (believe_me x) pad))
                                                         (prim__zextB32_B64 pad))
    | (S (S (S _)), S (S (S _))) = let pad = getPad {n=3} n in
                                   believe_me (prim__ashrB64 (prim__shlB64 (believe_me x) pad) pad)
    | _ = assert_unreachable

----signExtend : Bits n -> Bits (n+m)
--signExtend {m=m} (MkBits x) = MkBits (zeroUnused (sext' x))

-- TODO: Prove
trunc' : %static {m : Nat} -> %static {n : Nat} -> machineTy (nextBytes (m+n)) -> machineTy (nextBytes n)
trunc' {m=m} {n=n} x with (nextBytes n, nextBytes (m+n))
    | (Z, Z) = believe_me x
    | (Z, S Z) = believe_me (prim__truncB16_B8 (believe_me x))
    | (Z, S (S Z)) = believe_me (prim__truncB32_B8 (believe_me x))
    | (Z, S (S (S _))) = believe_me (prim__truncB64_B8 (believe_me x))
    | (S Z, S Z) = believe_me x
    | (S Z, S (S Z)) = believe_me (prim__truncB32_B16 (believe_me x))
    | (S Z, S (S (S _))) = believe_me (prim__truncB64_B16 (believe_me x))
    | (S (S Z), S (S Z)) = believe_me x
    | (S (S Z), S (S (S _))) = believe_me (prim__truncB64_B32 (believe_me x))
    | (S (S (S _)), S (S (S _))) = believe_me x
    | _ = assert_unreachable

truncate : %static {m : Nat} -> %static {n : Nat} -> Bits (m+n) -> Bits n
truncate (MkBits x) = MkBits (zeroUnused (trunc' x))

bitAt : %static {n : Nat} -> Fin n -> Bits n
bitAt n = intToBits 1 `shiftLeft` intToBits (cast n)

getBit : %static {n : Nat} -> Fin n -> Bits n -> Bool
getBit n x = (x `and` (bitAt n)) /= intToBits 0

setBit : %static {n : Nat} -> Fin n -> Bits n -> Bits n
setBit n x = x `or` (bitAt n)

unsetBit : %static {n : Nat} -> Fin n -> Bits n -> Bits n
unsetBit n x = x `and` complement (bitAt n)

bitsToStr : %static {n : Nat} -> Bits n -> String
bitsToStr x = pack (helper last x)
    where
      helper : %static {n : Nat} -> Fin (S n) -> Bits n -> List Char
      helper FZ _ = []
      helper (FS x) b = assert_total $ (if getBit x b then '1' else '0') :: helper (weaken x) b

implementation Show (Bits n) where
    show = bitsToStr

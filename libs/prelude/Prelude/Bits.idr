module Prelude.Bits

import Builtins

import Prelude.Algebra
import Prelude.Basics
import Prelude.Bool
import Prelude.Cast
import Prelude.Chars
import Prelude.Interfaces
import Prelude.Foldable
import Prelude.Functor
import Prelude.Nat
import Prelude.List
import Prelude.Strings

%access public export
%default total

--------------------------------------------------------------------------------
-- Convert to `List Bits8`
--------------------------------------------------------------------------------

||| Convert to list of `Bits8` with the most signficant byte at the
||| head.
b8ToBytes : Bits8 -> List Bits8
b8ToBytes b = [b]

||| Convert to list of `Bits8` with the most signficant byte at the
||| head.
b16ToBytes : Bits16 -> List Bits8
b16ToBytes b =
  [ prim__truncB16_B8 (prim__lshrB16 b 8)
  , prim__truncB16_B8 b
  ]

||| Convert to list of `Bits8` with the most signficant byte at the
||| head.
b32ToBytes : Bits32 -> List Bits8
b32ToBytes b =
  [ prim__truncB32_B8 (prim__lshrB32 b 24)
  , prim__truncB32_B8 (prim__lshrB32 b 16)
  , prim__truncB32_B8 (prim__lshrB32 b 8)
  , prim__truncB32_B8 b
  ]

||| Convert to list of `Bits8` with the most signficant byte at the
||| head.
b64ToBytes : Bits64 -> List Bits8
b64ToBytes b =
  [ prim__truncB64_B8 (prim__lshrB64 b 56)
  , prim__truncB64_B8 (prim__lshrB64 b 48)
  , prim__truncB64_B8 (prim__lshrB64 b 40)
  , prim__truncB64_B8 (prim__lshrB64 b 32)
  , prim__truncB64_B8 (prim__lshrB64 b 24)
  , prim__truncB64_B8 (prim__lshrB64 b 16)
  , prim__truncB64_B8 (prim__lshrB64 b 8)
  , prim__truncB64_B8 b
  ]

--------------------------------------------------------------------------------
-- Hex Strings
--------------------------------------------------------------------------------

||| Encode `Bits8` as a 2-character hex string.
b8ToHexString : Bits8 -> String
b8ToHexString c = pack [c1, c2]
  where getDigit : Bits8 -> Char
        getDigit b = let n = prim__zextB8_Int b in
                     if n >= 0 && n <= 9
                        then '0' `prim__addChar` cast n
                        else if n >= 10 && n <= 15
                                then 'A' `prim__addChar` cast (n - 10)
                                else '?' -- this is for totality - it should not happen
        c1 = getDigit (prim__andB8 (prim__lshrB8 c 4) 15)
        c2 = getDigit (prim__andB8 c 15)

||| Encode `Bits16` as a 4-character hex string.
b16ToHexString : Bits16 -> String
b16ToHexString c = concatMap b8ToHexString (b16ToBytes c)

||| Encode `Bits32` as an 8-character hex string.
b32ToHexString : Bits32 -> String
b32ToHexString c = concatMap b8ToHexString (b32ToBytes c)

||| Encode `Bits64` as a 16-character hex string.
b64ToHexString : Bits64 -> String
b64ToHexString c = concatMap b8ToHexString (b64ToBytes c)


--------------------------------------------------------------------------------
-- Binary Strings
--------------------------------------------------------------------------------

||| Encode `Bits8` as an 8-character binary string.
b8ToBinString : Bits8 -> String
b8ToBinString b = pack $ map (bitChar b) [7,6,5,4,3,2,1,0]
  where bitChar : Bits8 -> Bits8 -> Char
        bitChar b i = case b `prim__andB8` (1 `prim__shlB8` i) of
                           0 => '0'
                           _ => '1'

||| Encode `Bits16` as a 16-character binary string.
b16ToBinString : Bits16 -> String
b16ToBinString c = concatMap b8ToBinString (b16ToBytes c)

||| Encode `Bits32` as a 32-character binary string.
b32ToBinString : Bits32 -> String
b32ToBinString c = concatMap b8ToBinString (b32ToBytes c)

||| Encode `Bits64` as a 64-character binary string.
b64ToBinString : Bits64 -> String
b64ToBinString c = concatMap b8ToBinString (b64ToBytes c)


--------------------------------------------------------------------------------
-- Deprecated String Functions
--------------------------------------------------------------------------------

||| Encode `Bits8` as a 2-character hex string.
b8ToString : Bits8 -> String
b8ToString = b8ToHexString
%deprecate b8ToString "Please use `b8ToHexString` instead."

||| Encode `Bits16` as a 4-character hex string.
b16ToString : Bits16 -> String
b16ToString = b16ToHexString
%deprecate b16ToString "Please use `b16ToHexString` instead."

||| Encode `Bits32` as a 8-character hex string.
b32ToString : Bits32 -> String
b32ToString = b32ToHexString
%deprecate b32ToString "Please use `b32ToHexString` instead."

||| Encode `Bits64` as a 16-character hex string.
b64ToString : Bits64 -> String
b64ToString = b64ToHexString
%deprecate b64ToString "Please use `b64ToHexString` instead."

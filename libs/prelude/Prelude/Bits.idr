module Prelude.Bits

import Prelude.Strings
import Prelude.Vect
import Prelude.Bool

%access public
%default total


b8ToString : Bits8 -> String
b8ToString c = pack (with List [c1, c2])
  where getDigit : Bits8 -> Char
        getDigit b = let n = prim__zextB8_Int b in
                     if n >= 0 && n <= 9
                        then '0' `prim__addChar` cast n
                        else if n >= 10 && n <= 15
                                then 'A' `prim__addChar` cast (n - 10)
                                else '?' -- this is for totality - it should not happen
        c1 = getDigit (prim__andB8 (prim__lshrB8 c 4) 15)
        c2 = getDigit (prim__andB8 c 15)


b16ToString : Bits16 -> String
b16ToString c = c1 ++ c2 where
  c1 = b8ToString upper where
    upper : Bits8
    upper = prim__truncB16_B8 (prim__lshrB16 c 8)
  c2 = b8ToString lower where
    lower : Bits8
    lower = prim__truncB16_B8 c

b32ToString : Bits32 -> String
b32ToString c = c1 ++ c2 where
  c1 = b16ToString upper where
    upper : Bits16
    upper = prim__truncB32_B16 (prim__andB32 (prim__lshrB32 c 16) 0x0000ffff)
  c2 = b16ToString lower where
    lower : Bits16
    lower = prim__truncB32_B16 c

b64ToString : Bits64 -> String
b64ToString c = c1 ++ c2 where
  c1 = b32ToString upper where
    upper : Bits32
    upper = prim__truncB64_B32 (prim__andB64 (prim__lshrB64 c 32) 0x00000000ffffffff)
  c2 = b32ToString lower where
    lower : Bits32
    lower = prim__truncB64_B32 c

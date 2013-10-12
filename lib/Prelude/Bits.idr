module Prelude.Bits

import Prelude.Strings

%access public
%default total

private
hexVect : Vect 16 Char
hexVect = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
           'A', 'B', 'C', 'D', 'E', 'F']

private
toHexDigit : Fin 16 -> Char
toHexDigit n = index n hexVect

b8ToString : Bits8 -> String
b8ToString c = pack [c1, c2] where
  %assert_total -- We will only supply numbers that can fit in 4 bits
  toFin16 : Bits8 -> Fin 16
  toFin16 n = if n == 0
                 then fZ
                 else believe_me (fS (toFin16 (n-1)))
  c1 = toHexDigit upper where
    upper : Fin 16
    upper = toFin16 (prim__lshrB8 c 4)
  c2 = toHexDigit lower where
    lower : Fin 16
    lower = toFin16 (prim__andB8 c 0xf)

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
    upper = prim__truncB32_B16 (prim__lshrB32 c 16)
  c2 = b16ToString lower where
    lower : Bits16
    lower = prim__truncB32_B16 c

b64ToString : Bits64 -> String
b64ToString c = c1 ++ c2 where
  c1 = b32ToString upper where
    upper : Bits32
    upper = prim__truncB64_B32 (prim__lshrB64 c 32)
  c2 = b32ToString lower where
    lower : Bits32
    lower = prim__truncB64_B32 c

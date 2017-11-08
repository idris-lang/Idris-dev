-- ------------------------------------------------------------- [ Display.idr ]
-- Module    : Display.idr
-- Copyright : (c) The Idris Community.
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Some simple utilities to make the display fancier.
module Test.Unit.Display

%access export

fancyLine : Nat -> Char -> String
fancyLine l c = pack $ replicate l c

infoLine : String
infoLine = fancyLine 40 '-'

succLine : String
succLine = fancyLine 40 '='

errLine : String
errLine = fancyLine 40 '+'

heading : String -> String
heading n = unlines [infoLine, n, infoLine]


-- --------------------------------------------------------------------- [ EOF ]

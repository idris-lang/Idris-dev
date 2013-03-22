module Main

%dynamic "libm"

x : Float
x = unsafePerformIO (mkForeign (FFun "sin" [FFloat] FFloat) 1.6)

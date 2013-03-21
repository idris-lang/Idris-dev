module Main

%dynamic "libm.so"

x : Float
x = unsafePerformIO (mkForeign (FFun "sin" [FFloat] FFloat) 1.6)

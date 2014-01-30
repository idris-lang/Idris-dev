module Main

%dynamic "dummy", "libm", "msvcrt"

x : Float
x = unsafePerformIO (mkForeign (FFun "sin" [FFloat] FFloat) 1.6)

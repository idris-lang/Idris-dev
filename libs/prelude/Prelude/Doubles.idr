module Prelude.Doubles

import Builtins
import Prelude.Interfaces

%access public export
%default total

%include C "math.h"
%lib C "m"

pi : Double
pi = 3.14159265358979323846

euler : Double
euler = 2.7182818284590452354

exp : Double -> Double
exp x = prim__floatExp x

log : Double -> Double
log x = prim__floatLog x

sin : Double -> Double
sin x = prim__floatSin x

cos : Double -> Double
cos x = prim__floatCos x

tan : Double -> Double
tan x = prim__floatTan x

asin : Double -> Double
asin x = prim__floatASin x

acos : Double -> Double
acos x = prim__floatACos x

atan : Double -> Double
atan x = prim__floatATan x

atan2 : Double -> Double -> Double
atan2 y x = atan (y/x)

sinh : Double -> Double
sinh x = (exp x - exp (-x)) / 2

cosh : Double -> Double
cosh x = (exp x + exp (-x)) / 2

tanh : Double -> Double
tanh x = sinh x / cosh x

sqrt : Double -> Double
sqrt x = prim__floatSqrt x

floor : Double -> Double
floor x = prim__floatFloor x

ceiling : Double -> Double
ceiling x = prim__floatCeil x

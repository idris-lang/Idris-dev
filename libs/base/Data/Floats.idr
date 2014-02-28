module Data.Floats
-- this should really be Data.Float64
%access public
%default total

%include C "math.h"
%lib C "m"

pi : Float64
pi = 3.14159265358979323846 

euler : Float64
euler = 2.7182818284590452354

exp : Float64 -> Float64
exp x = prim__floatExp x

log : Float64 -> Float64
log x = prim__floatLog x

sin : Float64 -> Float64
sin x = prim__floatSin x

cos : Float64 -> Float64
cos x = prim__floatCos x

tan : Float64 -> Float64
tan x = prim__floatTan x

asin : Float64 -> Float64
asin x = prim__floatASin x

acos : Float64 -> Float64
acos x = prim__floatACos x

atan : Float64 -> Float64
atan x = prim__floatATan x

atan2 : Float64 -> Float64 -> Float64
atan2 y x = atan (y/x)

sinh : Float64 -> Float64
sinh x = (exp x - exp (-x)) / 2

cosh : Float64 -> Float64
cosh x = (exp x + exp (-x)) / 2

tanh : Float64 -> Float64
tanh x = sinh x / cosh x

sqrt : Float64 -> Float64
sqrt x = prim__floatSqrt x

floor : Float64 -> Float64
floor x = prim__floatFloor x

ceiling : Float64 -> Float64
ceiling x = prim__floatCeil x


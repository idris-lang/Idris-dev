module prelude.complex

import builtins


------------------------------ General

infix 6 :+
data Complex a = (:+) a a

realPart : Complex a -> a
realPart (r:+i) = r

imagPart : Complex a -> a
imagPart (r:+i) = i


------------------------------ Polarform

mkPolar : Float -> Float -> Complex Float
mkPolar radius angle = radius * cos angle :+ radius * sin angle

cis : Float -> Complex Float
cis angle = cos angle :+ sin angle

magnitude : Complex Float -> Float
magnitude (r:+i) = sqrt (r*r+i*i)

phase : Complex Float -> Float
phase (x:+y) = atan2 y x


------------------------------ Conjugate

conjugate : Num a => Complex a -> Complex a
conjugate (r:+i) = (r :+ (0-i))

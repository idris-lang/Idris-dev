{-
  (c) 2012 Copyright Mekeor Melire
-}


module Data.Complex

import Data.Floats

------------------------------ Rectangular form

infix 6 :+
data Complex a = (:+) a a

realPart : Complex a -> a
realPart (r:+i) = r

imagPart : Complex a -> a
imagPart (r:+i) = i

instance Eq a => Eq (Complex a) where
    (==) a b = realPart a == realPart b && imagPart a == imagPart b

instance Show a => Show (Complex a) where
    show (r:+i) = "("++show r++":+"++show i++")"



-- when we have a type class 'Fractional' (which contains Float32 and Float64),
-- we can do:
-- q: is that numerically stable?
-- float operations *need* to have good numerical stability!
{-
instance Fractional a => Fractional (Complex a) where
    (/) (a:+b) (c:+d) = let
                          real = (a*c+b*d)/(c*c+d*d)
                          imag = (b*c-a*d)/(c*c+d*d)
                        in
                          (real:+imag)
-}



------------------------------ Polarform

mkPolar : Float64 -> Float64 -> Complex Float64
mkPolar radius angle = radius * cos angle :+ radius * sin angle

cis : Float64 -> Complex Float64
cis angle = cos angle :+ sin angle

magnitude : Complex Float64 -> Float64
magnitude (r:+i) = sqrt (r*r+i*i)

phase : Complex Float64 -> Float64
phase (x:+y) = atan2 y x


------------------------------ Conjugate

conjugate : Num a => Complex a -> Complex a
conjugate (r:+i) = (r :+ (0-i))

-- We can't do "instance Num a => Num (Complex a)" because
-- we need "abs" which needs "magnitude" which needs "sqrt" which needs Float64
instance Num (Complex Float64) where
    (+) (a:+b) (c:+d) = ((a+b):+(c+d))
    (-) (a:+b) (c:+d) = ((a-b):+(c-d))
    (*) (a:+b) (c:+d) = ((a*c-b*d):+(b*c+a*d))
    fromInteger x = (fromInteger x:+0)
    abs (a:+b) = (magnitude (a:+b):+0)

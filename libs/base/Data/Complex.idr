{-
  (c) 2012 Copyright Mekeor Melire
-}


module Data.Complex

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
    showPrec d (r :+ i) = showParens (d >= plus_i) $ showPrec plus_i r ++ " :+ " ++ showPrec plus_i i
      where plus_i : Prec
            plus_i = User 6


-- when we have a type class 'Fractional' (which contains Float and Double),
-- we can do:
{-
instance Fractional a => Fractional (Complex a) where
    (/) (a:+b) (c:+d) = let
                          real = (a*c+b*d)/(c*c+d*d)
                          imag = (b*c-a*d)/(c*c+d*d)
                        in
                          (real:+imag)
-}



------------------------------ Polarform

mkPolar : Double -> Double -> Complex Double
mkPolar radius angle = radius * cos angle :+ radius * sin angle

cis : Double -> Complex Double
cis angle = cos angle :+ sin angle

magnitude : Complex Double -> Double
magnitude (r:+i) = sqrt (r*r+i*i)

phase : Complex Double -> Double
phase (x:+y) = atan2 y x


------------------------------ Conjugate

conjugate : Neg a => Complex a -> Complex a
conjugate (r:+i) = (r :+ (0-i))

instance Functor Complex where
    map f (r :+ i) = f r :+ f i

-- We can't do "instance Num a => Num (Complex a)" because
-- we need "abs" which needs "magnitude" which needs "sqrt" which needs Double
instance Num (Complex Double) where
    (+) (a:+b) (c:+d) = ((a+c):+(b+d))
    (*) (a:+b) (c:+d) = ((a*c-b*d):+(b*c+a*d))
    fromInteger x = (fromInteger x:+0)

instance Neg (Complex Double) where
    negate = map negate
    (-) (a:+b) (c:+d) = ((a-c):+(b-d))
    abs (a:+b) = (magnitude (a:+b):+0)


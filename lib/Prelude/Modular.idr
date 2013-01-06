module Prelude.Modular

import Prelude.Bits

%default total

-- Integers modulo 2^n
abstract
data Mod2 : Nat -> Type where
    MkMod2 : {n : Nat} -> Bits n -> Mod2 n

public
modAdd : Mod2 n -> Mod2 n -> Mod2 n
modAdd (MkMod2 x) (MkMod2 y) = MkMod2 (bitsAdd x y)

public
modSub : Mod2 n -> Mod2 n -> Mod2 n
modSub (MkMod2 x) (MkMod2 y) = MkMod2 (bitsSub x y)

public
modMul : Mod2 n -> Mod2 n -> Mod2 n
modMul (MkMod2 x) (MkMod2 y) = MkMod2 (bitsMul x y)

public
modDiv : Mod2 n -> Mod2 n -> Mod2 n
modDiv (MkMod2 x) (MkMod2 y) = MkMod2 (bitsUDiv x y)

public
modToStr : Mod2 n -> String
modToStr (MkMod2 x) = bitsToStr x

%assert_total
public
intToMod : {n : Nat} -> Int -> Mod2 n
intToMod {n=n} x = MkMod2 (intToBits x)

public
modToBits : Mod2 n -> Bits n
modToBits (MkMod2 x) = x

public
bitsToMod : Bits n -> Mod2 n
bitsToMod x = MkMod2 x

instance Num (Mod2 n) where
    (+) = modAdd
    (-) = modSub
    (*) = modMul
    abs = id
    fromInteger = intToMod

instance Cast (Mod2 n) (Bits n) where
    cast = modToBits

instance Cast (Bits n) (Mod2 n) where
    cast = bitsToMod

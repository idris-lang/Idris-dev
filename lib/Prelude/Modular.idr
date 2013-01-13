module Prelude.Modular

import Prelude.Bits

%default total

-- Integers modulo 2^n
public
data Mod2 : Nat -> Type where
    MkMod2 : {n : Nat} -> Bits n -> Mod2 n

modBin : (Bits n -> Bits n -> Bits n) -> Mod2 n -> Mod2 n -> Mod2 n
modBin f (MkMod2 x) (MkMod2 y) = MkMod2 (f x y)

modComp : (Bits n -> Bits n -> a) -> Mod2 n -> Mod2 n -> a
modComp f (MkMod2 x) (MkMod2 y) = f x y

public
modAdd : Mod2 n -> Mod2 n -> Mod2 n
modAdd = modBin bitsAdd

public
modSub : Mod2 n -> Mod2 n -> Mod2 n
modSub = modBin bitsSub

public
modMul : Mod2 n -> Mod2 n -> Mod2 n
modMul = modBin bitsMul

public partial
modDiv : Mod2 n -> Mod2 n -> Mod2 n
modDiv = modBin bitsUDiv

public partial
modRem : Mod2 n -> Mod2 n -> Mod2 n
modRem = modBin bitsURem

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

instance Eq (Mod2 n) where
    (==) = modComp (==)

instance Ord (Mod2 n) where
    (<) = modComp (<)
    (<=) = modComp (<=)
    (>=) = modComp (>=)
    (>) = modComp (>)
    compare = modComp compare

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

-- TODO: Other bases
public
modToStr : Mod2 n -> String
modToStr x = pack (reverse (helper x))
    where
      %assert_total
      helper : Mod2 n -> List Char
      helper x = strIndex "0123456789" (unsafeBitsToInt (modToBits (x `modRem` 10)))
                 :: (let q = (x `modDiv` 10) in
                     if q == 0 then [] else helper q)

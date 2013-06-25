{-# LANGUAGE RankNTypes, ScopedTypeVariables, PatternGuards #-}

module Idris.Primitives(elabPrims) where

import Idris.ElabDecls
import Idris.ElabTerm
import Idris.AbsSyntax

import IRTS.Lang

import Core.TT
import Core.Evaluate
import Data.Bits
import Data.Word
import Data.Int

data Prim = Prim { p_name  :: Name,
                   p_type  :: Type,
                   p_arity :: Int,
                   p_def   :: [Value] -> Maybe Value,
		   p_lexp  :: (Int, PrimFn),
                   p_total :: Totality
                 }

ty :: [Const] -> Const -> Type
ty []     x = Constant x
ty (t:ts) x = Bind (MN 0 "T") (Pi (Constant t)) (ty ts x)

believeTy :: Type
believeTy = Bind (UN "a") (Pi (TType (UVar (-2))))
            (Bind (UN "b") (Pi (TType (UVar (-2))))
            (Bind (UN "x") (Pi (V 1)) (V 1)))

total, partial :: Totality
total = Total []
partial = Partial NotCovering

primitives :: [Prim]
primitives =
   -- operators
  [Prim (UN "prim__eqChar")  (ty [ChType, ChType] IType) 2 (bcBin (==))
     (2, LEq ITNative) total,
   Prim (UN "prim__ltChar")  (ty [ChType, ChType] IType) 2 (bcBin (<))
     (2, LLt ITNative) total,
   Prim (UN "prim__lteChar") (ty [ChType, ChType] IType) 2 (bcBin (<=))
     (2, LLe ITNative) total,
   Prim (UN "prim__gtChar")  (ty [ChType, ChType] IType) 2 (bcBin (>))
     (2, LGt ITNative) total,
   Prim (UN "prim__gteChar") (ty [ChType, ChType] IType) 2 (bcBin (>=))
     (2, LGe ITNative) total,

   iCoerce IT8 IT16 "zext" zext LZExt,
   iCoerce IT8 IT32 "zext" zext LZExt,
   iCoerce IT8 IT64 "zext" zext LZExt,
   iCoerce IT8 ITBig "zext" zext LZExt,
   iCoerce IT8 ITNative "zext" zext LZExt,
   iCoerce IT16 IT32 "zext" zext LZExt,
   iCoerce IT16 IT64 "zext" zext LZExt,
   iCoerce IT16 ITBig "zext" zext LZExt,
   iCoerce IT16 ITNative "zext" zext LZExt,
   iCoerce IT32 IT64 "zext" zext LZExt,
   iCoerce IT32 ITBig "zext" zext LZExt,
   iCoerce IT32 ITNative "zext" zext LZExt,
   iCoerce IT64 ITBig "zext" zext LZExt,
   iCoerce ITNative ITBig "zext" zext LZExt,
   iCoerce ITNative IT64 "zext" zext LZExt,
   iCoerce ITNative IT32 "zext" zext LZExt,
   iCoerce ITNative IT16 "zext" zext LZExt,

   iCoerce IT8 IT16 "sext" sext LSExt,
   iCoerce IT8 IT32 "sext" sext LSExt,
   iCoerce IT8 IT64 "sext" sext LSExt,
   iCoerce IT8 ITBig "sext" sext LSExt,
   iCoerce IT8 ITNative "sext" sext LSExt,
   iCoerce IT16 IT32 "sext" sext LSExt,
   iCoerce IT16 IT64 "sext" sext LSExt,
   iCoerce IT16 ITBig "sext" sext LSExt,
   iCoerce IT16 ITNative "sext" sext LSExt,
   iCoerce IT32 IT64 "sext" sext LSExt,
   iCoerce IT32 ITBig "sext" sext LSExt,
   iCoerce IT32 ITNative "sext" sext LSExt,
   iCoerce IT64 ITBig "sext" sext LSExt,
   iCoerce ITNative ITBig "sext" sext LSExt,
   iCoerce ITNative ITBig "sext" sext LSExt,
   iCoerce ITNative IT64 "sext" sext LSExt,
   iCoerce ITNative IT32 "sext" sext LSExt,
   iCoerce ITNative IT16 "sext" sext LSExt,

   iCoerce IT16 IT8 "trunc" trunc LTrunc,
   iCoerce IT32 IT8 "trunc" trunc LTrunc,
   iCoerce IT64 IT8 "trunc" trunc LTrunc,
   iCoerce ITBig IT8 "trunc" trunc LTrunc,
   iCoerce ITNative IT8 "trunc" trunc LTrunc,
   iCoerce IT32 IT16 "trunc" trunc LTrunc,
   iCoerce IT64 IT16 "trunc" trunc LTrunc,
   iCoerce ITBig IT16 "trunc" trunc LTrunc,
   iCoerce ITNative IT16 "trunc" trunc LTrunc,
   iCoerce IT64 IT32 "trunc" trunc LTrunc,
   iCoerce ITBig IT32 "trunc" trunc LTrunc,
   iCoerce ITNative IT32 "trunc" trunc LTrunc,
   iCoerce ITBig IT64 "trunc" trunc LTrunc,
   iCoerce IT16 ITNative "trunc" trunc LTrunc,
   iCoerce IT32 ITNative "trunc" trunc LTrunc,
   iCoerce IT64 ITNative "trunc" trunc LTrunc,
   iCoerce ITBig ITNative "trunc" trunc LTrunc,
   iCoerce ITNative IT64 "trunc" trunc LTrunc,

   Prim (UN "prim__addFloat") (ty [FlType, FlType] FlType) 2 (fBin (+))
     (2, LFPlus) total,
   Prim (UN "prim__subFloat") (ty [FlType, FlType] FlType) 2 (fBin (-))
     (2, LFMinus) total,
   Prim (UN "prim__mulFloat") (ty [FlType, FlType] FlType) 2 (fBin (*))
     (2, LFTimes) total,
   Prim (UN "prim__divFloat") (ty [FlType, FlType] FlType) 2 (fBin (/))
     (2, LFDiv) total,
   Prim (UN "prim__eqFloat")  (ty [FlType, FlType] IType) 2 (bfBin (==))
     (2, LFEq) total,
   Prim (UN "prim__ltFloat")  (ty [FlType, FlType] IType) 2 (bfBin (<))
     (2, LFLt) total,
   Prim (UN "prim__lteFloat") (ty [FlType, FlType] IType) 2 (bfBin (<=))
     (2, LFLe) total,
   Prim (UN "prim__gtFloat")  (ty [FlType, FlType] IType) 2 (bfBin (>))
     (2, LFGt) total,
   Prim (UN "prim__gteFloat") (ty [FlType, FlType] IType) 2 (bfBin (>=))
     (2, LFGe) total,
   Prim (UN "prim__concat") (ty [StrType, StrType] StrType) 2 (sBin (++))
    (2, LStrConcat) total,
   Prim (UN "prim__eqString") (ty [StrType, StrType] IType) 2 (bsBin (==))
    (2, LStrEq) total,
   Prim (UN "prim__ltString") (ty [StrType, StrType] IType) 2 (bsBin (<))
    (2, LStrLt) total,
   Prim (UN "prim_lenString") (ty [StrType] IType) 1 (p_strLen)
    (1, LStrLen) total,
    -- Conversions
   Prim (UN "prim__charToInt") (ty [ChType] IType) 1 (c_charToInt)
     (1, LChInt ITNative) total,
   Prim (UN "prim__intToChar") (ty [IType] ChType) 1 (c_intToChar)
     (1, LIntCh ITNative) total,
   Prim (UN "prim__strToFloat") (ty [StrType] FlType) 1 (c_strToFloat)
     (1, LStrFloat) total,
   Prim (UN "prim__floatToStr") (ty [FlType] StrType) 1 (c_floatToStr)
     (1, LFloatStr) total,

   Prim (UN "prim__floatExp") (ty [FlType] FlType) 1 (p_floatExp)
     (1, LFExp) total,
   Prim (UN "prim__floatLog") (ty [FlType] FlType) 1 (p_floatLog)
     (1, LFLog) total,
   Prim (UN "prim__floatSin") (ty [FlType] FlType) 1 (p_floatSin)
     (1, LFSin) total,
   Prim (UN "prim__floatCos") (ty [FlType] FlType) 1 (p_floatCos)
     (1, LFCos) total,
   Prim (UN "prim__floatTan") (ty [FlType] FlType) 1 (p_floatTan)
     (1, LFTan) total,
   Prim (UN "prim__floatASin") (ty [FlType] FlType) 1 (p_floatASin)
     (1, LFASin) total,
   Prim (UN "prim__floatACos") (ty [FlType] FlType) 1 (p_floatACos)
     (1, LFACos) total,
   Prim (UN "prim__floatATan") (ty [FlType] FlType) 1 (p_floatATan)
     (1, LFATan) total,
   Prim (UN "prim__floatSqrt") (ty [FlType] FlType) 1 (p_floatSqrt)
     (1, LFSqrt) total,
   Prim (UN "prim__floatFloor") (ty [FlType] FlType) 1 (p_floatFloor)
     (1, LFFloor) total,
   Prim (UN "prim__floatCeil") (ty [FlType] FlType) 1 (p_floatCeil)
     (1, LFCeil) total,

   Prim (UN "prim__strHead") (ty [StrType] ChType) 1 (p_strHead)
     (1, LStrHead) partial,
   Prim (UN "prim__strTail") (ty [StrType] StrType) 1 (p_strTail)
     (1, LStrTail) partial,
   Prim (UN "prim__strCons") (ty [ChType, StrType] StrType) 2 (p_strCons)
    (2, LStrCons) total,
   Prim (UN "prim__strIndex") (ty [StrType, IType] ChType) 2 (p_strIndex)
    (2, LStrIndex) partial,
   Prim (UN "prim__strRev") (ty [StrType] StrType) 1 (p_strRev)
    (1, LStrRev) total,
   Prim (UN "prim__readString") (ty [PtrType] StrType) 1 (p_cantreduce)
     (1, LReadStr) partial,
   Prim (UN "prim__vm") (ty [] PtrType) 0 (p_cantreduce)
     (0, LVMPtr) total,
   -- Streams
   Prim (UN "prim__stdin") (ty [] PtrType) 0 (p_cantreduce)
    (0, LStdIn) partial,
   Prim (UN "prim__believe_me") believeTy 3 (p_believeMe)
    (3, LNoOp) partial -- ahem
  ] ++ concatMap intOps [IT8, IT16, IT32, IT64, ITBig, ITNative]

intOps :: IntTy -> [Prim]
intOps ity =
    [ iCmp ity "lt" (bCmp ity (<)) LLt total
    , iCmp ity "lte" (bCmp ity (<=)) LLe total
    , iCmp ity "eq" (bCmp ity (==)) LEq total
    , iCmp ity "gte" (bCmp ity (>=)) LGe total
    , iCmp ity "gt" (bCmp ity (>)) LGt total
    , iBinOp ity "add" (bitBin ity (+)) LPlus total
    , iBinOp ity "sub" (bitBin ity (-)) LMinus total
    , iBinOp ity "mul" (bitBin ity (*)) LTimes total
    , iBinOp ity "udiv" (bitBin ity div) LUDiv partial
    , iBinOp ity "sdiv" (bsdiv ity) LSDiv partial
    , iBinOp ity "urem" (bitBin ity rem) LURem partial
    , iBinOp ity "srem" (bsrem ity) LSRem partial
    , iBinOp ity "shl" (bitBin ity (\x y -> shiftL x (fromIntegral y))) LSHL total
    , iBinOp ity "lshr" (bitBin ity (\x y -> shiftR x (fromIntegral y))) LLSHR total
    , iBinOp ity "ashr" (bashr ity) LASHR total
    , iBinOp ity "and" (bitBin ity (.&.)) LAnd total
    , iBinOp ity "or" (bitBin ity (.|.)) LOr total
    , iBinOp ity "xor" (bitBin ity (xor)) LXOr total
    , iUnOp ity "compl" (bUn ity complement) LCompl total
    , Prim (UN $ "prim__toStr" ++ intTyName ity) (ty [intTyToConst ity] StrType) 1 intToStr
               (1, LIntStr ity) total
    , Prim (UN $ "prim__fromStr" ++ intTyName ity) (ty [StrType] (intTyToConst ity)) 1 (strToInt ity)
               (1, LStrInt ity) total
    , Prim (UN $ "prim__toFloat" ++ intTyName ity) (ty [intTyToConst ity] FlType) 1 intToFloat
               (1, LIntFloat ity) total
    , Prim (UN $ "prim__fromFloat" ++ intTyName ity) (ty [FlType] (intTyToConst ity)) 1 (floatToInt ity)
               (1, LFloatInt ity) total
    ]

intTyName :: IntTy -> String
intTyName ITNative = "Int"
intTyName ITBig = "BigInt"
intTyName sized = "B" ++ show (intTyWidth sized)

iCmp, iBinOp, iUnOp :: IntTy -> String -> ([Value] -> Maybe Value) -> (IntTy -> PrimFn) -> Totality -> Prim
iCmp ity op impl irop totality = Prim (UN $ "prim__" ++ op ++ intTyName ity) (ty (replicate 2 $ intTyToConst ity) IType) 2 impl (2, irop ity) totality
iBinOp ity op impl irop totality = Prim (UN $ "prim__" ++ op ++ intTyName ity) (ty (replicate 2 $ intTyToConst ity) (intTyToConst ity)) 2 impl (2, irop ity) totality
iUnOp ity op impl irop totality = Prim (UN $ "prim__" ++ op ++ intTyName ity) (ty [intTyToConst ity] (intTyToConst ity)) 1 impl (1, irop ity) totality

iCoerce :: IntTy -> IntTy -> String -> (IntTy -> IntTy -> [Value] -> Maybe Value) -> (IntTy -> IntTy -> PrimFn) -> Prim
iCoerce from to op impl irop =
    Prim (UN $ "prim__" ++ op ++ intTyName from ++ "_" ++ intTyName to)
             (ty [intTyToConst from] (intTyToConst to)) 1 (impl from to) (1, irop from to) total

p_believeMe :: [a] -> Maybe a
p_believeMe [_,_,x] = Just x
p_believeMe _ = Nothing

iUn :: (Int -> Int) -> [Value] -> Maybe Value
iUn op [VConstant (I x)] = Just $ VConstant (I (op x))
iUn _ _ = Nothing

iBin :: (Int -> Int -> Int) -> [Value] -> Maybe Value
iBin op [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (op x y))
iBin _ _ = Nothing

bBin :: (Integer -> Integer -> Integer) -> [Value] -> Maybe Value
bBin op [VConstant (BI x), VConstant (BI y)] = Just $ VConstant (BI (op x y))
bBin _ _ = Nothing

bBini :: (Integer -> Integer -> Int) -> [Value] -> Maybe Value
bBini op [VConstant (BI x), VConstant (BI y)] = Just $ VConstant (I (op x y))
bBini _ _ = Nothing

biBin :: (Int -> Int -> Bool) -> [Value] -> Maybe Value
biBin op = iBin (\x y -> if (op x y) then 1 else 0)

bbBin :: (Integer -> Integer -> Bool) -> [Value] -> Maybe Value
bbBin op = bBini (\x y -> if (op x y) then 1 else 0)

fBin :: (Double -> Double -> Double) -> [Value] -> Maybe Value
fBin op [VConstant (Fl x), VConstant (Fl y)] = Just $ VConstant (Fl (op x y))
fBin _ _ = Nothing

bfBin :: (Double -> Double -> Bool) -> [Value] -> Maybe Value
bfBin op [VConstant (Fl x), VConstant (Fl y)] = let i = (if op x y then 1 else 0) in
                                                Just $ VConstant (I i)
bfBin _ _ = Nothing

bcBin :: (Char -> Char -> Bool) -> [Value] -> Maybe Value
bcBin op [VConstant (Ch x), VConstant (Ch y)] = let i = (if op x y then 1 else 0) in
                                                Just $ VConstant (I i)
bcBin _ _ = Nothing

bsBin :: (String -> String -> Bool) -> [Value] -> Maybe Value
bsBin op [VConstant (Str x), VConstant (Str y)]
    = let i = (if op x y then 1 else 0) in
          Just $ VConstant (I i)
bsBin _ _ = Nothing

sBin :: (String -> String -> String) -> [Value] -> Maybe Value
sBin op [VConstant (Str x), VConstant (Str y)] = Just $ VConstant (Str (op x y))
sBin _ _ = Nothing

bsrem :: IntTy -> [Value] -> Maybe Value
bsrem IT8 [VConstant (B8 x), VConstant (B8 y)]
    = Just $ VConstant (B8 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int8)))
bsrem IT16 [VConstant (B16 x), VConstant (B16 y)]
    = Just $ VConstant (B16 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int16)))
bsrem IT32 [VConstant (B32 x), VConstant (B32 y)]
    = Just $ VConstant (B32 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int32)))
bsrem IT64 [VConstant (B64 x), VConstant (B64 y)]
    = Just $ VConstant (B64 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int64)))
bsrem ITNative [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (x `rem` y))
bsrem _ _ = Nothing

bsdiv :: IntTy -> [Value] -> Maybe Value
bsdiv IT8 [VConstant (B8 x), VConstant (B8 y)]
    = Just $ VConstant (B8 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int8)))
bsdiv IT16 [VConstant (B16 x), VConstant (B16 y)]
    = Just $ VConstant (B16 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int16)))
bsdiv IT32 [VConstant (B32 x), VConstant (B32 y)]
    = Just $ VConstant (B32 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int32)))
bsdiv IT64 [VConstant (B64 x), VConstant (B64 y)]
    = Just $ VConstant (B64 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int64)))
bsdiv ITNative [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (x `div` y))
bsdiv _ _ = Nothing

bashr :: IntTy -> [Value] -> Maybe Value
bashr IT8 [VConstant (B8 x), VConstant (B8 y)]
    = Just $ VConstant (B8 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int8)))
bashr IT16 [VConstant (B16 x), VConstant (B16 y)]
    = Just $ VConstant (B16 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int16)))
bashr IT32 [VConstant (B32 x), VConstant (B32 y)]
    = Just $ VConstant (B32 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int32)))
bashr IT64 [VConstant (B64 x), VConstant (B64 y)]
    = Just $ VConstant (B64 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int64)))
bashr ITNative [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (x `shiftR` y))
bashr _ _ = Nothing

bUn :: IntTy -> (forall a. Bits a => a -> a) -> [Value] -> Maybe Value
bUn IT8  op [VConstant (B8  x)] = Just $ VConstant (B8  (op x))
bUn IT16 op [VConstant (B16 x)] = Just $ VConstant (B16 (op x))
bUn IT32 op [VConstant (B32 x)] = Just $ VConstant (B32 (op x))
bUn IT64 op [VConstant (B64 x)] = Just $ VConstant (B64 (op x))
bUn ITBig op [VConstant (BI x)] = Just $ VConstant (BI (op x))
bUn ITNative op [VConstant (I x)] = Just $ VConstant (I (op x))
bUn _ _ _ = Nothing

bitBin :: IntTy -> (forall a. (Bits a, Integral a) => a -> a -> a) -> [Value] -> Maybe Value
bitBin IT8  op [VConstant (B8  x), VConstant (B8  y)] = Just $ VConstant (B8  (op x y))
bitBin IT16 op [VConstant (B16 x), VConstant (B16 y)] = Just $ VConstant (B16 (op x y))
bitBin IT32 op [VConstant (B32 x), VConstant (B32 y)] = Just $ VConstant (B32 (op x y))
bitBin IT64 op [VConstant (B64 x), VConstant (B64 y)] = Just $ VConstant (B64 (op x y))
bitBin ITBig op [VConstant (BI x), VConstant (BI y)] = Just $ VConstant (BI (op x y))
bitBin ITNative op [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (op x y))
bitBin _ _ _ = Nothing

bCmp :: IntTy -> (forall a. Ord a => a -> a -> Bool) -> [Value] -> Maybe Value
bCmp IT8  op [VConstant (B8  x), VConstant (B8  y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp IT16 op [VConstant (B16 x), VConstant (B16 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp IT32 op [VConstant (B32 x), VConstant (B32 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp IT64 op [VConstant (B64 x), VConstant (B64 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp ITBig op [VConstant (BI x), VConstant (BI y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp ITNative op [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp _ _ _ = Nothing

toInt :: Integral a => IntTy -> a -> Value
toInt IT8  x = VConstant (B8 (fromIntegral x))
toInt IT16 x = VConstant (B16 (fromIntegral x))
toInt IT32 x = VConstant (B32 (fromIntegral x))
toInt IT64 x = VConstant (B64 (fromIntegral x))
toInt ITBig x = VConstant (BI (fromIntegral x))
toInt ITNative x = VConstant (I (fromIntegral x))

intToInt :: IntTy -> IntTy -> [Value] -> Maybe Value
intToInt IT8 out [VConstant (B8 x)] = Just $ toInt out x
intToInt IT16 out [VConstant (B16 x)] = Just $ toInt out x
intToInt IT32 out [VConstant (B32 x)] = Just $ toInt out x
intToInt IT64 out [VConstant (B64 x)] = Just $ toInt out x
intToInt ITBig out [VConstant (BI x)] = Just $ toInt out x
intToInt ITNative out [VConstant (I x)] = Just $ toInt out x
intToInt _ _ _ = Nothing

zext :: IntTy -> IntTy -> [Value] -> Maybe Value
zext from ITBig val = intToInt from ITBig val
zext ITBig _ _ = Nothing
zext from to val
    | intTyWidth from < intTyWidth to = intToInt from to val
zext _ _ _ = Nothing

sext :: IntTy -> IntTy -> [Value] -> Maybe Value
sext IT8  out [VConstant (B8  x)] = Just $ toInt out (fromIntegral x :: Int8)
sext IT16 out [VConstant (B16 x)] = Just $ toInt out (fromIntegral x :: Int16)
sext IT32 out [VConstant (B32 x)] = Just $ toInt out (fromIntegral x :: Int32)
sext IT64 out [VConstant (B64 x)] = Just $ toInt out (fromIntegral x :: Int64)
sext ITBig _ _ = Nothing
sext from to val = intToInt from to val

trunc :: IntTy -> IntTy -> [Value] -> Maybe Value
trunc ITBig to val = intToInt ITBig to val
trunc _ ITBig _ = Nothing
trunc from to val | intTyWidth from > intTyWidth to = intToInt from to val
trunc _ _ _ = Nothing

getInt :: [Value] -> Maybe Integer
getInt [VConstant (B8 x)] = Just . toInteger $ x
getInt [VConstant (B16 x)] = Just . toInteger $ x
getInt [VConstant (B32 x)] = Just . toInteger $ x
getInt [VConstant (B64 x)] = Just . toInteger $ x
getInt [VConstant (I x)] = Just . toInteger $ x
getInt [VConstant (BI x)] = Just x
getInt _ = Nothing

intToStr :: [Value] -> Maybe Value
intToStr val | Just i <- getInt val = Just $ VConstant (Str (show i))
intToStr _ = Nothing

strToInt :: IntTy -> [Value] -> Maybe Value
strToInt ity [VConstant (Str x)] = case reads x of
                                     [(n,"")] -> Just $ toInt ity (n :: Integer)
                                     _ -> Just $ VConstant (I 0)
strToInt _ _ = Nothing

intToFloat :: [Value] -> Maybe Value
intToFloat val | Just i <- getInt val = Just $ VConstant (Fl (fromIntegral i))
intToFloat _ = Nothing

floatToInt :: IntTy -> [Value] -> Maybe Value
floatToInt ity [VConstant (Fl x)] = Just $ toInt ity (truncate x :: Integer)
floatToInt _ _ = Nothing

c_intToChar :: [Value] -> Maybe Value
c_intToChar [VConstant (I x)] = Just $ VConstant (Ch (toEnum x))
c_intToChar _ = Nothing
c_charToInt [VConstant (Ch x)] = Just $ VConstant (I (fromEnum x))
c_charToInt _ = Nothing

c_floatToStr :: [Value] -> Maybe Value
c_floatToStr [VConstant (Fl x)] = Just $ VConstant (Str (show x))
c_floatToStr _ = Nothing
c_strToFloat [VConstant (Str x)] = case reads x of
                                        [(n,"")] -> Just $ VConstant (Fl n)
                                        _ -> Just $ VConstant (Fl 0)
c_strToFloat _ = Nothing

p_fPrim :: (Double -> Double) -> [Value] -> Maybe Value
p_fPrim f [VConstant (Fl x)] = Just $ VConstant (Fl (f x))
p_fPrim f _ = Nothing

p_floatExp, p_floatLog, p_floatSin, p_floatCos, p_floatTan, p_floatASin, p_floatACos, p_floatATan, p_floatSqrt, p_floatFloor, p_floatCeil :: [Value] -> Maybe Value
p_floatExp = p_fPrim exp
p_floatLog = p_fPrim log
p_floatSin = p_fPrim sin
p_floatCos = p_fPrim cos
p_floatTan = p_fPrim tan
p_floatASin = p_fPrim asin
p_floatACos = p_fPrim acos
p_floatATan = p_fPrim atan
p_floatSqrt = p_fPrim sqrt
p_floatFloor = p_fPrim (fromInteger . floor)
p_floatCeil = p_fPrim (fromInteger . ceiling)

p_strLen, p_strHead, p_strTail, p_strIndex, p_strCons, p_strRev :: [Value] -> Maybe Value
p_strLen [VConstant (Str xs)] = Just $ VConstant (I (length xs))
p_strLen _ = Nothing
p_strHead [VConstant (Str (x:xs))] = Just $ VConstant (Ch x)
p_strHead _ = Nothing
p_strTail [VConstant (Str (x:xs))] = Just $ VConstant (Str xs)
p_strTail _ = Nothing
p_strIndex [VConstant (Str xs), VConstant (I i)]
   | i < length xs = Just $ VConstant (Ch (xs!!i))
p_strIndex _ = Nothing
p_strCons [VConstant (Ch x), VConstant (Str xs)] = Just $ VConstant (Str (x:xs))
p_strCons _ = Nothing
p_strRev [VConstant (Str xs)] = Just $ VConstant (Str (reverse xs))
p_strRev _ = Nothing

p_cantreduce :: a -> Maybe b
p_cantreduce _ = Nothing

elabPrim :: Prim -> Idris ()
elabPrim (Prim n ty i def sc tot)
    = do updateContext (addOperator n ty i def)
         setTotality n tot
         i <- getIState
         putIState i { idris_scprims = (n, sc) : idris_scprims i }

elabPrims :: Idris ()
elabPrims = do mapM_ (elabDecl EAll toplevel)
                     (map (PData "" defaultSyntax (FC "builtin" 0) False)
                         [inferDecl, unitDecl, falseDecl, pairDecl, eqDecl])
               mapM_ elabPrim primitives


{-|
Module      : Idris.Primitives
Description : Provision of primitive data types.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards, RankNTypes, ScopedTypeVariables #-}

module Idris.Primitives(primitives, Prim(..)) where

import Idris.AbsSyntax
import Idris.Core.Evaluate
import Idris.Core.TT
import IRTS.Lang

import Data.Bits
import Data.Char
import Data.Function (on)
import Data.Int
import qualified Data.Vector.Unboxed as V
import Data.Word
import Debug.Trace

data Prim = Prim { p_name  :: Name,
                   p_type  :: Type,
                   p_arity :: Int,
                   p_def   :: [Const] -> Maybe Const,
                   p_lexp  :: (Int, PrimFn),
                   p_total :: Totality
                 }

ty :: [Const] -> Const -> Type
ty []     x = Constant x
ty (t:ts) x = Bind (sMN 0 "T") (Pi RigW Nothing (Constant t) (TType (UVar [] (-3)))) (ty ts x)

total, partial, iopartial :: Totality
total = Total []
partial = Partial NotCovering
iopartial = Partial ExternalIO

primitives :: [Prim]
primitives =
   -- operators
  [iCoerce (ITFixed IT8) (ITFixed IT16) "zext" zext LZExt,
   iCoerce (ITFixed IT8) (ITFixed IT32) "zext" zext LZExt,
   iCoerce (ITFixed IT8) (ITFixed IT64) "zext" zext LZExt,
   iCoerce (ITFixed IT8) ITBig "zext" zext LZExt,
   iCoerce (ITFixed IT8) ITNative "zext" zext LZExt,
   iCoerce (ITFixed IT16) (ITFixed IT32) "zext" zext LZExt,
   iCoerce (ITFixed IT16) (ITFixed IT64) "zext" zext LZExt,
   iCoerce (ITFixed IT16) ITBig "zext" zext LZExt,
   iCoerce (ITFixed IT16) ITNative "zext" zext LZExt,
   iCoerce (ITFixed IT32) (ITFixed IT64) "zext" zext LZExt,
   iCoerce (ITFixed IT32) ITBig "zext" zext LZExt,
   iCoerce (ITFixed IT32) ITNative "zext" zext LZExt,
   iCoerce (ITFixed IT64) ITBig "zext" zext LZExt,
   iCoerce ITNative ITBig "zext" zext LZExt,
   iCoerce ITNative (ITFixed IT64) "zext" zext LZExt,
   iCoerce ITNative (ITFixed IT32) "zext" zext LZExt,
   iCoerce ITNative (ITFixed IT16) "zext" zext LZExt,
   iCoerce ITChar ITBig "zext" zext LZExt,

   iCoerce (ITFixed IT8) (ITFixed IT16) "sext" sext LSExt,
   iCoerce (ITFixed IT8) (ITFixed IT32) "sext" sext LSExt,
   iCoerce (ITFixed IT8) (ITFixed IT64) "sext" sext LSExt,
   iCoerce (ITFixed IT8) ITBig "sext" sext LSExt,
   iCoerce (ITFixed IT8) ITNative "sext" sext LSExt,
   iCoerce (ITFixed IT16) (ITFixed IT32) "sext" sext LSExt,
   iCoerce (ITFixed IT16) (ITFixed IT64) "sext" sext LSExt,
   iCoerce (ITFixed IT16) ITBig "sext" sext LSExt,
   iCoerce (ITFixed IT16) ITNative "sext" sext LSExt,
   iCoerce (ITFixed IT32) (ITFixed IT64) "sext" sext LSExt,
   iCoerce (ITFixed IT32) ITBig "sext" sext LSExt,
   iCoerce (ITFixed IT32) ITNative "sext" sext LSExt,
   iCoerce (ITFixed IT64) ITBig "sext" sext LSExt,
   iCoerce ITNative ITBig "sext" sext LSExt,
   iCoerce ITNative ITBig "sext" sext LSExt,
   iCoerce ITNative (ITFixed IT64) "sext" sext LSExt,
   iCoerce ITNative (ITFixed IT32) "sext" sext LSExt,
   iCoerce ITNative (ITFixed IT16) "sext" sext LSExt,
   iCoerce ITChar ITBig "sext" sext LSExt,

   iCoerce (ITFixed IT16) (ITFixed IT8) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT32) (ITFixed IT8) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT64) (ITFixed IT8) "trunc" trunc LTrunc,
   iCoerce ITBig (ITFixed IT8) "trunc" trunc LTrunc,
   iCoerce ITNative (ITFixed IT8) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT32) (ITFixed IT16) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT64) (ITFixed IT16) "trunc" trunc LTrunc,
   iCoerce ITBig (ITFixed IT16) "trunc" trunc LTrunc,
   iCoerce ITNative (ITFixed IT16) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT64) (ITFixed IT32) "trunc" trunc LTrunc,
   iCoerce ITBig (ITFixed IT32) "trunc" trunc LTrunc,
   iCoerce ITNative (ITFixed IT32) "trunc" trunc LTrunc,
   iCoerce ITBig (ITFixed IT64) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT16) ITNative "trunc" trunc LTrunc,
   iCoerce (ITFixed IT32) ITNative "trunc" trunc LTrunc,
   iCoerce (ITFixed IT64) ITNative "trunc" trunc LTrunc,
   iCoerce ITBig ITNative "trunc" trunc LTrunc,
   iCoerce ITNative (ITFixed IT64) "trunc" trunc LTrunc,
   iCoerce ITBig ITChar "trunc" trunc LTrunc,

   Prim (sUN "prim__addFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType ATFloat)) 2 (fBin (+))
     (2, LPlus ATFloat) total,
   Prim (sUN "prim__subFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType ATFloat)) 2 (fBin (-))
     (2, LMinus ATFloat) total,
   Prim (sUN "prim__mulFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType ATFloat)) 2 (fBin (*))
     (2, LTimes ATFloat) total,
   Prim (sUN "prim__divFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType ATFloat)) 2 (fBin (/))
     (2, LSDiv ATFloat) total,
   Prim (sUN "prim__eqFloat")  (ty [(AType ATFloat), (AType ATFloat)] (AType (ATInt ITNative))) 2 (bfBin (==))
     (2, LEq ATFloat) total,
   Prim (sUN "prim__sltFloat")  (ty [(AType ATFloat), (AType ATFloat)] (AType (ATInt ITNative))) 2 (bfBin (<))
     (2, LSLt ATFloat) total,
   Prim (sUN "prim__slteFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType (ATInt ITNative))) 2 (bfBin (<=))
     (2, LSLe ATFloat) total,
   Prim (sUN "prim__sgtFloat")  (ty [(AType ATFloat), (AType ATFloat)] (AType (ATInt ITNative))) 2 (bfBin (>))
     (2, LSGt ATFloat) total,
   Prim (sUN "prim__sgteFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType (ATInt ITNative))) 2 (bfBin (>=))
     (2, LSGe ATFloat) total,
   Prim (sUN "prim__concat") (ty [StrType, StrType] StrType) 2 (sBin (++))
    (2, LStrConcat) total,
   Prim (sUN "prim__eqString") (ty [StrType, StrType] (AType (ATInt ITNative))) 2 (bsBin (==))
    (2, LStrEq) total,
   Prim (sUN "prim__ltString") (ty [StrType, StrType] (AType (ATInt ITNative))) 2 (bsBin (<))
    (2, LStrLt) total,
   Prim (sUN "prim_lenString") (ty [StrType] (AType (ATInt ITNative))) 1 (p_strLen)
    (1, LStrLen) total,
    -- Conversions
   Prim (sUN "prim__charToInt") (ty [(AType (ATInt ITChar))] (AType (ATInt ITNative))) 1 (c_charToInt)
     (1, LChInt ITNative) total,
   Prim (sUN "prim__intToChar") (ty [(AType (ATInt ITNative))] (AType (ATInt ITChar))) 1 (c_intToChar)
     (1, LIntCh ITNative) partial,
   Prim (sUN "prim__strToFloat") (ty [StrType] (AType ATFloat)) 1 (c_strToFloat)
     (1, LStrFloat) total,
   Prim (sUN "prim__floatToStr") (ty [(AType ATFloat)] StrType) 1 (c_floatToStr)
     (1, LFloatStr) total,

   Prim (sUN "prim__floatExp") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatExp)
     (1, LFExp) total,
   Prim (sUN "prim__floatLog") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatLog)
     (1, LFLog) total,
   Prim (sUN "prim__floatSin") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatSin)
     (1, LFSin) total,
   Prim (sUN "prim__floatCos") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatCos)
     (1, LFCos) total,
   Prim (sUN "prim__floatTan") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatTan)
     (1, LFTan) total,
   Prim (sUN "prim__floatASin") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatASin)
     (1, LFASin) total,
   Prim (sUN "prim__floatACos") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatACos)
     (1, LFACos) total,
   Prim (sUN "prim__floatATan") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatATan)
     (1, LFATan) total,
   Prim (sUN "prim__floatSqrt") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatSqrt)
     (1, LFSqrt) total,
   Prim (sUN "prim__floatFloor") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatFloor)
     (1, LFFloor) total,
   Prim (sUN "prim__floatCeil") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatCeil)
     (1, LFCeil) total,
   Prim (sUN "prim__negFloat") (ty [(AType ATFloat)] (AType ATFloat)) 1 (c_negFloat)
     (1, LFNegate) total,

   Prim (sUN "prim__strHead") (ty [StrType] (AType (ATInt ITChar))) 1 (p_strHead)
     (1, LStrHead) partial,
   Prim (sUN "prim__strTail") (ty [StrType] StrType) 1 (p_strTail)
     (1, LStrTail) partial,
   Prim (sUN "prim__strCons") (ty [(AType (ATInt ITChar)), StrType] StrType) 2 (p_strCons)
    (2, LStrCons) total,
   Prim (sUN "prim__strIndex") (ty [StrType, (AType (ATInt ITNative))] (AType (ATInt ITChar))) 2 (p_strIndex)
    (2, LStrIndex) partial,
   Prim (sUN "prim__strRev") (ty [StrType] StrType) 1 (p_strRev)
    (1, LStrRev) total,
   Prim (sUN "prim__strSubstr") (ty [AType (ATInt ITNative), AType (ATInt ITNative), StrType] StrType) 3 (p_strSubstr)
    (3, LStrSubstr) total,

   Prim (sUN "prim__readString") (ty [WorldType] StrType) 1 (p_cantreduce)
     (1, LReadStr) total, -- total is okay, because we have 'WorldType'
   Prim (sUN "prim__writeString") (ty [WorldType,StrType] (AType (ATInt ITNative))) 2 (p_cantreduce)
     (2, LWriteStr) total,
    Prim (sUN "prim__systemInfo") (ty [AType (ATInt ITNative)] StrType) 1 (p_cantreduce)
        (1, LSystemInfo) total
  ] ++ concatMap intOps [ITFixed IT8, ITFixed IT16, ITFixed IT32, ITFixed IT64, ITBig, ITNative, ITChar]

intOps :: IntTy -> [Prim]
intOps ity = intCmps ity ++ intArith ity ++ intConv ity

intSCmps :: IntTy -> [Prim]
intSCmps ity =
    [ iCmp ity "slt" False (bCmp ity (sCmpOp ity (<))) (LSLt . ATInt) total
    , iCmp ity "slte" False (bCmp ity (sCmpOp ity (<=))) (LSLe . ATInt) total
    , iCmp ity "eq" False (bCmp ity (==)) (LEq . ATInt) total
    , iCmp ity "sgte" False (bCmp ity (sCmpOp ity (>=))) (LSGe . ATInt) total
    , iCmp ity "sgt" False (bCmp ity (sCmpOp ity (>))) (LSGt . ATInt) total
    ]

intCmps :: IntTy -> [Prim]
intCmps ITNative = intSCmps ITNative
intCmps ity =
    intSCmps ity ++
    [ iCmp ity "lt" False (bCmp ity (cmpOp ity (<))) LLt total
    , iCmp ity "lte" False (bCmp ity (cmpOp ity (<=))) LLe total
    , iCmp ity "gte" False (bCmp ity (cmpOp ity (>=))) LGe total
    , iCmp ity "gt" False (bCmp ity (cmpOp ity (>))) LGt total
    ]

intArith :: IntTy -> [Prim]
intArith ity =
    [ iBinOp ity "add" (bitBin ity (+)) (LPlus . ATInt) total
    , iBinOp ity "sub" (bitBin ity (-)) (LMinus . ATInt) total
    , iBinOp ity "mul" (bitBin ity (*)) (LTimes . ATInt) total
    , iBinOp ity "udiv" (bitBin ity div) LUDiv partial
    , iBinOp ity "sdiv" (bsdiv ity) (LSDiv . ATInt) partial
    , iBinOp ity "urem" (bitBin ity rem) LURem partial
    , iBinOp ity "srem" (bsrem ity) (LSRem . ATInt) partial
    , iBinOp ity "shl" (bitBin ity (\x y -> shiftL x (fromIntegral y))) LSHL total
    , iBinOp ity "lshr" (bitBin ity (\x y -> shiftR x (fromIntegral y))) LLSHR total
    , iBinOp ity "ashr" (bashr ity) LASHR total
    , iBinOp ity "and" (bitBin ity (.&.)) LAnd total
    , iBinOp ity "or" (bitBin ity (.|.)) LOr total
    , iBinOp ity "xor" (bitBin ity (xor)) LXOr total
    , iUnOp ity "compl" (bUn ity complement) LCompl total
    ]

intConv :: IntTy -> [Prim]
intConv ity =
    [ Prim (sUN $ "prim__toStr" ++ intTyName ity) (ty [AType . ATInt $ ity] StrType) 1 intToStr
               (1, LIntStr ity) total
    , Prim (sUN $ "prim__fromStr" ++ intTyName ity) (ty [StrType] (AType . ATInt $ ity)) 1 (strToInt ity)
               (1, LStrInt ity) total
    , Prim (sUN $ "prim__toFloat" ++ intTyName ity) (ty [AType . ATInt $ ity] (AType ATFloat)) 1 intToFloat
               (1, LIntFloat ity) total
    , Prim (sUN $ "prim__fromFloat" ++ intTyName ity) (ty [AType ATFloat] (AType . ATInt $ ity)) 1 (floatToInt ity)
               (1, LFloatInt ity) total
    ]

bitcastPrim :: ArithTy -> ArithTy -> (ArithTy -> [Const] -> Maybe Const) -> PrimFn -> Prim
bitcastPrim from to impl prim =
    Prim (sUN $ "prim__bitcast" ++ aTyName from ++ "_" ++ aTyName to) (ty [AType from] (AType to)) 1 (impl to)
         (1, prim) total

concatWord8 :: (Word8, Word8) -> Word16
concatWord8 (high, low) = fromIntegral high .|. (fromIntegral low `shiftL` 8)

concatWord16 :: (Word16, Word16) -> Word32
concatWord16 (high, low) = fromIntegral high .|. (fromIntegral low `shiftL` 16)

concatWord32 :: (Word32, Word32) -> Word64
concatWord32 (high, low) = fromIntegral high .|. (fromIntegral low `shiftL` 32)

truncWord16 :: Bool -> Word16 -> Word8
truncWord16 True x = fromIntegral (x `shiftR` 8)
truncWord16 False x = fromIntegral x

truncWord32 :: Bool -> Word32 -> Word16
truncWord32 True x = fromIntegral (x `shiftR` 16)
truncWord32 False x = fromIntegral x

truncWord64 :: Bool -> Word64 -> Word32
truncWord64 True x = fromIntegral (x `shiftR` 32)
truncWord64 False x = fromIntegral x

aTyName :: ArithTy -> String
aTyName (ATInt t) = intTyName t
aTyName ATFloat = "Float"

iCmp  :: IntTy -> String -> Bool -> ([Const] -> Maybe Const) -> (IntTy -> PrimFn) -> Totality -> Prim
iCmp ity op self impl irop totality
    = Prim (sUN $ "prim__" ++ op ++ intTyName ity)
      (ty (replicate 2 . AType . ATInt $ ity) (AType (ATInt (if self then ity else ITNative))))
      2 impl (2, irop ity) totality

iBinOp, iUnOp :: IntTy -> String -> ([Const] -> Maybe Const) -> (IntTy -> PrimFn) -> Totality -> Prim
iBinOp ity op impl irop totality
    = Prim (sUN $ "prim__" ++ op ++ intTyName ity)
      (ty (replicate 2  . AType . ATInt $ ity) (AType . ATInt $ ity))
      2 impl (2, irop ity) totality
iUnOp ity op impl irop totality
    = Prim (sUN $ "prim__" ++ op ++ intTyName ity)
      (ty [AType . ATInt $ ity] (AType . ATInt $ ity))
      1 impl (1, irop ity) totality

iCoerce :: IntTy -> IntTy -> String -> (IntTy -> IntTy -> [Const] -> Maybe Const) -> (IntTy -> IntTy -> PrimFn) -> Prim
iCoerce from to op impl irop =
    Prim (sUN $ "prim__" ++ op ++ intTyName from ++ "_" ++ intTyName to)
             (ty [AType . ATInt $ from] (AType . ATInt $ to)) 1 (impl from to) (1, irop from to) total

fBin :: (Double -> Double -> Double) -> [Const] -> Maybe Const
fBin op [Fl x, Fl y] = Just $ Fl (op x y)
fBin _ _ = Nothing

bfBin :: (Double -> Double -> Bool) -> [Const] -> Maybe Const
bfBin op [Fl x, Fl y] = let i = (if op x y then 1 else 0) in
                        Just $ I i
bfBin _ _ = Nothing

bcBin :: (Char -> Char -> Bool) -> [Const] -> Maybe Const
bcBin op [Ch x, Ch y] = let i = (if op x y then 1 else 0) in
                        Just $ I i
bcBin _ _ = Nothing

bsBin :: (String -> String -> Bool) -> [Const] -> Maybe Const
bsBin op [Str x, Str y]
    = let i = (if op x y then 1 else 0) in
          Just $ I i
bsBin _ _ = Nothing

sBin :: (String -> String -> String) -> [Const] -> Maybe Const
sBin op [Str x, Str y] = Just $ Str (op x y)
sBin _ _ = Nothing

bsrem :: IntTy -> [Const] -> Maybe Const
bsrem ITBig [BI x, BI y] = Just . BI $ x `rem` y
bsrem (ITFixed IT8) [B8 x, B8 y]
    = Just $ B8 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int8))
bsrem (ITFixed IT16) [B16 x, B16 y]
    = Just $ B16 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int16))
bsrem (ITFixed IT32) [B32 x, B32 y]
    = Just $ B32 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int32))
bsrem (ITFixed IT64) [B64 x, B64 y]
    = Just $ B64 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int64))
bsrem ITNative [I x, I y] = Just $ I (x `rem` y)
bsrem ITChar [Ch x, Ch y] = Just $ Ch (chr $ (ord x) `rem` (ord y))
bsrem _ _ = Nothing

bsdiv :: IntTy -> [Const] -> Maybe Const
bsdiv ITBig [BI x, BI y] = Just . BI $ x `div` y
bsdiv (ITFixed IT8) [B8 x, B8 y]
    = Just $ B8 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int8))
bsdiv (ITFixed IT16) [B16 x, B16 y]
    = Just $ B16 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int16))
bsdiv (ITFixed IT32) [B32 x, B32 y]
    = Just $ B32 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int32))
bsdiv (ITFixed IT64) [B64 x, B64 y]
    = Just $ B64 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int64))
bsdiv ITNative [I x, I y] = Just $ I (x `div` y)
bsdiv ITChar [Ch x, Ch y] = Just $ Ch (chr $ (ord x) `div` (ord y))
bsdiv _ _ = Nothing

bashr :: IntTy -> [Const] -> Maybe Const
bashr ITBig [BI x, BI y] = Just $ BI (x `shiftR` fromIntegral y)
bashr (ITFixed IT8) [B8 x, B8 y]
    = Just $ B8 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int8))
bashr (ITFixed IT16) [B16 x, B16 y]
    = Just $ B16 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int16))
bashr (ITFixed IT32) [B32 x, B32 y]
    = Just $ B32 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int32))
bashr (ITFixed IT64) [B64 x, B64 y]
    = Just $ B64 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int64))
bashr ITNative [I x, I y] = Just $ I (x `shiftR` y)
bashr ITChar [Ch x, Ch y] = Just $ Ch (chr $ (ord x) `shiftR` (ord y))
bashr _ _ = Nothing

bUn :: IntTy -> (forall a. Bits a => a -> a) -> [Const] -> Maybe Const
bUn (ITFixed IT8)      op [B8  x] = Just $ B8  (op x)
bUn (ITFixed IT16)     op [B16 x] = Just $ B16 (op x)
bUn (ITFixed IT32)     op [B32 x] = Just $ B32 (op x)
bUn (ITFixed IT64)     op [B64 x] = Just $ B64 (op x)
bUn ITBig    op [BI x]  = Just $ BI (op x)
bUn ITNative op [I x]   = Just $ I (op x)
bUn ITChar op [Ch x] = Just $ Ch (chr $ op (ord x))
bUn _        _   _      = Nothing

bitBin :: IntTy -> (forall a. (Bits a, Integral a) => a -> a -> a) -> [Const] -> Maybe Const
bitBin (ITFixed IT8)      op [B8  x, B8  y] = Just $ B8  (op x y)
bitBin (ITFixed IT16)     op [B16 x, B16 y] = Just $ B16 (op x y)
bitBin (ITFixed IT32)     op [B32 x, B32 y] = Just $ B32 (op x y)
bitBin (ITFixed IT64)     op [B64 x, B64 y] = Just $ B64 (op x y)
bitBin ITBig    op [BI x,  BI y]  = Just $ BI (op x y)
bitBin ITNative op [I x,   I y]   = Just $ I (op x y)
bitBin ITChar   op [Ch x,  Ch y]   = Just $ Ch (chr $ op (ord x) (ord y))
bitBin _        _  _              = Nothing

bCmp :: IntTy -> (forall a. (Integral a, Ord a) => a -> a -> Bool) -> [Const] -> Maybe Const
bCmp (ITFixed IT8)      op [B8  x, B8  y] = Just $ I (if (op x y) then 1 else 0)
bCmp (ITFixed IT16)     op [B16 x, B16 y] = Just $ I (if (op x y) then 1 else 0)
bCmp (ITFixed IT32)     op [B32 x, B32 y] = Just $ I (if (op x y) then 1 else 0)
bCmp (ITFixed IT64)     op [B64 x, B64 y] = Just $ I (if (op x y) then 1 else 0)
bCmp ITBig    op [BI x, BI y]   = Just $ I (if (op x y) then 1 else 0)
bCmp ITNative op [I x, I y]     = Just $ I (if (op x y) then 1 else 0)
bCmp ITChar   op [Ch x, Ch y]     = Just $ I (if (op (ord x) (ord y)) then 1 else 0)
bCmp _        _  _              = Nothing


cmpOp :: (Ord a, Integral a) => IntTy -> (forall b. Ord b => b -> b -> Bool) -> a -> a -> Bool
cmpOp (ITFixed _) f = f
cmpOp (ITNative)  f = f `on` (fromIntegral :: Integral a => a -> Word)
cmpOp (ITChar)    f = f `on` ((fromIntegral :: Integral a => a -> Word))
cmpOp _ f = let xor = (/=) in (\ x y -> (f x y) `xor` (x < 0) `xor` (y < 0))

sCmpOp :: (Ord a, Integral a) => IntTy -> (forall b. Ord b => b -> b -> Bool) -> a -> a -> Bool
sCmpOp (ITFixed IT8) f = f `on` (fromIntegral :: Integral a => a -> Int8)
sCmpOp (ITFixed IT16) f = f `on` (fromIntegral :: Integral a => a -> Int16)
sCmpOp (ITFixed IT32) f = f `on` (fromIntegral :: Integral a => a -> Int32)
sCmpOp (ITFixed IT64) f = f `on` (fromIntegral :: Integral a => a -> Int64)
sCmpOp _ f = f

toInt :: Integral a => IntTy -> a -> Const
toInt (ITFixed IT8)      x = B8 (fromIntegral x)
toInt (ITFixed IT16)     x = B16 (fromIntegral x)
toInt (ITFixed IT32)     x = B32 (fromIntegral x)
toInt (ITFixed IT64)     x = B64 (fromIntegral x)
toInt ITBig    x = BI (fromIntegral x)
toInt ITNative x = I (fromIntegral x)
toInt ITChar x = Ch (chr $ fromIntegral x)

intToInt :: IntTy -> IntTy -> [Const] -> Maybe Const
intToInt (ITFixed IT8)      out [B8  x] = Just $ toInt out x
intToInt (ITFixed IT16)     out [B16 x] = Just $ toInt out x
intToInt (ITFixed IT32)     out [B32 x] = Just $ toInt out x
intToInt (ITFixed IT64)     out [B64 x] = Just $ toInt out x
intToInt ITBig              out [BI  x] = Just $ toInt out x
intToInt ITNative           out [I   x] = Just $ toInt out x
intToInt ITChar             out [Ch  x] = Just $ toInt out (ord x)
intToInt _ _ _ = Nothing

zext :: IntTy -> IntTy -> [Const] -> Maybe Const
zext from ITBig val = intToInt from ITBig val
zext ITBig _ _ = Nothing
zext f@(ITFixed from) t@(ITFixed to) val
    | nativeTyWidth from < nativeTyWidth to = intToInt f t val
zext ITNative to [I x] = Just $ toInt to (fromIntegral x :: Word)
zext from ITNative val = intToInt from ITNative val
zext _ _ _ = Nothing

sext :: IntTy -> IntTy -> [Const] -> Maybe Const
sext (ITFixed IT8)  out [B8  x] = Just $ toInt out (fromIntegral x :: Int8)
sext (ITFixed IT16) out [B16 x] = Just $ toInt out (fromIntegral x :: Int16)
sext (ITFixed IT32) out [B32 x] = Just $ toInt out (fromIntegral x :: Int32)
sext (ITFixed IT64) out [B64 x] = Just $ toInt out (fromIntegral x :: Int64)
sext ITBig _  _       = Nothing
sext from to  val     = intToInt from to val

trunc :: IntTy -> IntTy -> [Const] -> Maybe Const
trunc ITBig to val = intToInt ITBig to val
trunc _ ITBig _ = Nothing
trunc f@(ITFixed from) t@(ITFixed to) val | nativeTyWidth from > nativeTyWidth to = intToInt f t val
trunc ITNative to [I x] = Just $ toInt to x
trunc from ITNative val = intToInt from ITNative val
trunc _ _ _ = Nothing

intToStr :: [Const] -> Maybe Const
intToStr val | [i] <- getInt val = Just $ Str (show i)
intToStr _ = Nothing

getInt :: [Const] -> [Integer]
getInt (B8 x : xs) = toInteger x : getInt xs
getInt (B16 x : xs) = toInteger x : getInt xs
getInt (B32 x : xs) = toInteger x : getInt xs
getInt (B64 x : xs) = toInteger x : getInt xs
getInt (I x : xs) = toInteger x : getInt xs
getInt (BI x : xs) = x : getInt xs
getInt _ = []

strToInt :: IntTy -> [Const] -> Maybe Const
strToInt ity [Str x] = case reads x of
                         [(n,s)] -> Just $ if all isSpace s then toInt ity (n :: Integer) else I 0
                         _       -> Just $ I 0
strToInt _ _ = Nothing

intToFloat :: [Const] -> Maybe Const
intToFloat val | [i] <- getInt val = Just $ Fl (fromIntegral i)
intToFloat _ = Nothing

floatToInt :: IntTy -> [Const] -> Maybe Const
floatToInt ity [Fl x] = Just $ toInt ity (truncate x :: Integer)
floatToInt _ _ = Nothing

c_intToChar, c_charToInt :: [Const] -> Maybe Const
c_intToChar [(I x)] = Just . Ch . toEnum $ x
c_intToChar _ = Nothing
c_charToInt [(Ch x)] = Just . I . fromEnum $ x
c_charToInt _ = Nothing

c_negFloat :: [Const] -> Maybe Const
c_negFloat [Fl x] = Just $ Fl (negate x)
c_negFloat _      = Nothing

c_floatToStr :: [Const] -> Maybe Const
c_floatToStr [Fl x] = Just $ Str (show x)
c_floatToStr _ = Nothing
c_strToFloat [Str x] = case reads x of
                         [(n,s)] -> Just $ Fl (if all isSpace s then n else 0)
                         _       -> Just $ Fl 0
c_strToFloat _ = Nothing

p_fPrim :: (Double -> Double) -> [Const] -> Maybe Const
p_fPrim f [Fl x] = Just $ Fl (f x)
p_fPrim f _ = Nothing

p_floatExp, p_floatLog, p_floatSin, p_floatCos, p_floatTan, p_floatASin, p_floatACos, p_floatATan, p_floatSqrt, p_floatFloor, p_floatCeil :: [Const] -> Maybe Const
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

p_strLen, p_strHead, p_strTail, p_strIndex, p_strCons, p_strRev, p_strSubstr :: [Const] -> Maybe Const
p_strLen [Str xs] = Just $ I (length xs)
p_strLen _ = Nothing
p_strHead [Str (x:xs)] = Just $ Ch x
p_strHead _ = Nothing
p_strTail [Str (x:xs)] = Just $ Str xs
p_strTail _ = Nothing
p_strIndex [Str xs, I i]
   | i < length xs = Just $ Ch (xs!!i)
p_strIndex _ = Nothing
p_strCons [Ch x, Str xs] = Just $ Str (x:xs)
p_strCons _ = Nothing
p_strRev [Str xs] = Just $ Str (reverse xs)
p_strRev _ = Nothing
p_strSubstr [I offset, I length, Str input] = Just $ Str (take length (drop offset input))
p_strSubstr _ = Nothing


p_cantreduce :: a -> Maybe b
p_cantreduce _ = Nothing

{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

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

ty []     x = Constant x
ty (t:ts) x = Bind (MN 0 "T") (Pi (Constant t)) (ty ts x)

believeTy = Bind (UN "a") (Pi (TType (UVar (-2))))
            (Bind (UN "b") (Pi (TType (UVar (-2))))
            (Bind (UN "x") (Pi (V 1)) (V 1)))

total = Total []
partial = Partial NotCovering 

primitives =
   -- operators
  [Prim (UN "prim__addInt") (ty [IType, IType] IType) 2 (iBin (+))
    (2, LPlus ITNative) total,
   Prim (UN "prim__subInt") (ty [IType, IType] IType) 2 (iBin (-))
     (2, LMinus ITNative) total,
   Prim (UN "prim__mulInt") (ty [IType, IType] IType) 2 (iBin (*))
     (2, LTimes ITNative) total,
   Prim (UN "prim__divInt") (ty [IType, IType] IType) 2 (iBin div)
     (2, LSDiv ITNative) partial,
   Prim (UN "prim__modInt") (ty [IType, IType] IType) 2 (iBin mod)
     (2, LSRem ITNative) partial,
   Prim (UN "prim__andInt") (ty [IType, IType] IType) 2 (iBin (.&.))
     (2, LAnd ITNative) partial,
   Prim (UN "prim__orInt") (ty [IType, IType] IType) 2 (iBin (.|.))
     (2, LOr ITNative) partial,
   Prim (UN "prim__xorInt") (ty [IType, IType] IType) 2 (iBin xor)
     (2, LXOr ITNative) partial,
   Prim (UN "prim__shLInt") (ty [IType, IType] IType) 2 (iBin shiftL)
     (2, LSHL ITNative) partial,
   Prim (UN "prim__shRInt") (ty [IType, IType] IType) 2 (iBin shiftR)
     (2, LASHR ITNative) partial,
   Prim (UN "prim__complInt") (ty [IType] IType) 1 (iUn complement)
     (1, LCompl ITNative) partial,
   Prim (UN "prim__eqInt")  (ty [IType, IType] IType) 2 (biBin (==))
     (2, LEq ITNative) total,
   Prim (UN "prim__ltInt")  (ty [IType, IType] IType) 2 (biBin (<))
     (2, LLt ITNative) total,
   Prim (UN "prim__lteInt") (ty [IType, IType] IType) 2 (biBin (<=))
     (2, LLe ITNative) total,
   Prim (UN "prim__gtInt")  (ty [IType, IType] IType) 2 (biBin (>))
     (2, LGt ITNative) total,
   Prim (UN "prim__gteInt") (ty [IType, IType] IType) 2 (biBin (>=))
     (2, LGe ITNative) total,
   Prim (UN "prim__eqChar")  (ty [ChType, ChType] IType) 2 (bcBin (==))
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
   iCoerce IT16 IT32 "zext" zext LZExt,
   iCoerce IT16 IT64 "zext" zext LZExt,
   iCoerce IT32 IT64 "zext" zext LZExt,

   iCoerce IT8 IT16 "sext" sext LSExt,
   iCoerce IT8 IT32 "sext" sext LSExt,
   iCoerce IT8 IT64 "sext" sext LSExt,
   iCoerce IT16 IT32 "sext" sext LSExt,
   iCoerce IT16 IT64 "sext" sext LSExt,
   iCoerce IT32 IT64 "sext" sext LSExt,

   iCoerce IT16 IT8 "trunc" trunc LTrunc,
   iCoerce IT32 IT8 "trunc" trunc LTrunc,
   iCoerce IT64 IT8 "trunc" trunc LTrunc,
   iCoerce IT32 IT16 "trunc" trunc LTrunc,
   iCoerce IT64 IT16 "trunc" trunc LTrunc,
   iCoerce IT64 IT32 "trunc" trunc LTrunc,

   Prim (UN "prim__intToB8") (ty [IType] B8Type) 1 intToBits8
    (1, LIntB8) total,
   Prim (UN "prim__intToB16") (ty [IType] B16Type) 1 intToBits16
    (1, LIntB16) total,
   Prim (UN "prim__intToB32") (ty [IType] B32Type) 1 intToBits32
    (1, LIntB32) total,
   Prim (UN "prim__intToB64") (ty [IType] B64Type) 1 intToBits64
    (1, LIntB64) total,
   Prim (UN "prim__B32ToInt") (ty [B32Type] IType) 1 bits32ToInt
    (1, LB32Int) total,

   Prim (UN "prim__addBigInt") (ty [BIType, BIType] BIType) 2 (bBin (+))
    (2, LBPlus) total,
   Prim (UN "prim__subBigInt") (ty [BIType, BIType] BIType) 2 (bBin (-))
     (2, LBMinus) total,
   Prim (UN "prim__mulBigInt") (ty [BIType, BIType] BIType) 2 (bBin (*))
     (2, LBTimes) total,
   Prim (UN "prim__divBigInt") (ty [BIType, BIType] BIType) 2 (bBin div)
     (2, LBDiv) partial,
   Prim (UN "prim__modBigInt") (ty [BIType, BIType] BIType) 2 (bBin mod)
     (2, LBMod) partial,
   Prim (UN "prim__eqBigInt")  (ty [BIType, BIType] IType) 2 (bbBin (==))
     (2, LBEq) total,
   Prim (UN "prim__ltBigInt")  (ty [BIType, BIType] IType) 2 (bbBin (<))
     (2, LBLt) total,
   Prim (UN "prim__lteBigInt")  (ty [BIType, BIType] IType) 2 (bbBin (<=))
     (2, LBLe) total,
   Prim (UN "prim__gtBigInt")  (ty [BIType, BIType] IType) 2 (bbBin (>))
     (2, LBGt) total,
   Prim (UN "prim__gtBigInt")  (ty [BIType, BIType] IType) 2 (bbBin (>=))
     (2, LBGe) total,
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
   Prim (UN "prim__strToInt") (ty [StrType] IType) 1 (c_strToInt)
     (1, LStrInt) total,
   Prim (UN "prim__intToStr") (ty [IType] StrType) 1 (c_intToStr)
     (1, LIntStr) total,
   Prim (UN "prim__charToInt") (ty [ChType] IType) 1 (c_charToInt)
     (1, LChInt) total,
   Prim (UN "prim__intToChar") (ty [IType] ChType) 1 (c_intToChar)
     (1, LIntCh) total,
   Prim (UN "prim__intToBigInt") (ty [IType] BIType) 1 (c_intToBigInt)
     (1, LIntBig) total,
   Prim (UN "prim__bigIntToInt") (ty [BIType] IType) 1 (c_bigIntToInt)
     (1, LBigInt) total,
   Prim (UN "prim__strToBigInt") (ty [StrType] BIType) 1 (c_strToBigInt)
     (1, LStrBig) total,
   Prim (UN "prim__bigIntToStr") (ty [BIType] StrType) 1 (c_bigIntToStr)
     (1, LBigStr) total,
   Prim (UN "prim__strToFloat") (ty [StrType] FlType) 1 (c_strToFloat)
     (1, LStrFloat) total,
   Prim (UN "prim__floatToStr") (ty [FlType] StrType) 1 (c_floatToStr)
     (1, LFloatStr) total,
   Prim (UN "prim__intToFloat") (ty [IType] FlType) 1 (c_intToFloat)
     (1, LIntFloat) total,
   Prim (UN "prim__floatToInt") (ty [FlType] IType) 1 (c_floatToInt)
     (1, LFloatInt) total,

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
  ] ++ concatMap intOps [IT8, IT16, IT32, IT64]

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
    ]

iCmp ity op impl irop totality = Prim (UN $ "prim__" ++ op ++ "B" ++ show (intTyWidth ity)) (ty (replicate 2 $ intTyToConst ity) IType) 2 impl (2, irop ity) totality
iBinOp ity op impl irop totality = Prim (UN $ "prim__" ++ op ++ "B" ++ show (intTyWidth ity)) (ty (replicate 2 $ intTyToConst ity) (intTyToConst ity)) 2 impl (2, irop ity) totality
iUnOp ity op impl irop totality = Prim (UN $ "prim__" ++ op ++ "B" ++ show (intTyWidth ity)) (ty [intTyToConst ity] (intTyToConst ity)) 1 impl (1, irop ity) totality
iCoerce from to op impl irop =
    Prim (UN $ "prim__" ++ op ++ "B" ++ show (intTyWidth from) ++ "_" ++ show (intTyWidth to))
             (ty [intTyToConst from] (intTyToConst to)) 1 (impl from to) (1, irop from to) total

p_believeMe [_,_,x] = Just x
p_believeMe _ = Nothing

iUn op [VConstant (I x)] = Just $ VConstant (I (op x))
iUn _ _ = Nothing

iBin op [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (op x y))
iBin _ _ = Nothing

bBin op [VConstant (BI x), VConstant (BI y)] = Just $ VConstant (BI (op x y))
bBin _ _ = Nothing

bBini op [VConstant (BI x), VConstant (BI y)] = Just $ VConstant (I (op x y))
bBini _ _ = Nothing

biBin op = iBin (\x y -> if (op x y) then 1 else 0)
bbBin op = bBini (\x y -> if (op x y) then 1 else 0)

fBin op [VConstant (Fl x), VConstant (Fl y)] = Just $ VConstant (Fl (op x y))
fBin _ _ = Nothing

bfBin op [VConstant (Fl x), VConstant (Fl y)] = let i = (if op x y then 1 else 0) in
                                                Just $ VConstant (I i)
bfBin _ _ = Nothing

bcBin op [VConstant (Ch x), VConstant (Ch y)] = let i = (if op x y then 1 else 0) in
                                                Just $ VConstant (I i)
bcBin _ _ = Nothing

bsBin op [VConstant (Str x), VConstant (Str y)] 
    = let i = (if op x y then 1 else 0) in
          Just $ VConstant (I i)
bsBin _ _ = Nothing

sBin op [VConstant (Str x), VConstant (Str y)] = Just $ VConstant (Str (op x y))
sBin _ _ = Nothing

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
bUn _ _ _ = Nothing

bitBin :: IntTy -> (forall a. (Bits a, Integral a) => a -> a -> a) -> [Value] -> Maybe Value
bitBin IT8  op [VConstant (B8  x), VConstant (B8  y)] = Just $ VConstant (B8  (op x y))
bitBin IT16 op [VConstant (B16 x), VConstant (B16 y)] = Just $ VConstant (B16 (op x y))
bitBin IT32 op [VConstant (B32 x), VConstant (B32 y)] = Just $ VConstant (B32 (op x y))
bitBin IT64 op [VConstant (B64 x), VConstant (B64 y)] = Just $ VConstant (B64 (op x y))
bitBin _ _ _ = Nothing

bCmp :: IntTy -> (forall a. Ord a => a -> a -> Bool) -> [Value] -> Maybe Value
bCmp IT8  op [VConstant (B8  x), VConstant (B8  y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp IT16 op [VConstant (B16 x), VConstant (B16 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp IT32 op [VConstant (B32 x), VConstant (B32 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp IT64 op [VConstant (B64 x), VConstant (B64 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp _ _ _ = Nothing

toB IT8  x = VConstant (B8 (fromIntegral x))
toB IT16 x = VConstant (B16 (fromIntegral x))
toB IT32 x = VConstant (B32 (fromIntegral x))
toB IT64 x = VConstant (B64 (fromIntegral x))

zext IT8  IT16 [VConstant (B8  x)] = Just $ VConstant (B16 (fromIntegral x))
zext IT8  IT32 [VConstant (B8  x)] = Just $ VConstant (B32 (fromIntegral x))
zext IT8  IT64 [VConstant (B8  x)] = Just $ VConstant (B64 (fromIntegral x))
zext IT16 IT32 [VConstant (B16 x)] = Just $ VConstant (B32 (fromIntegral x))
zext IT16 IT64 [VConstant (B16 x)] = Just $ VConstant (B64 (fromIntegral x))
zext IT32 IT64 [VConstant (B32 x)] = Just $ VConstant (B64 (fromIntegral x))
zext _ _ _ = Nothing

sext IT8  IT16 [VConstant (B8  x)] = Just $ VConstant (B16 (fromIntegral (fromIntegral x :: Int8)))
sext IT8  IT32 [VConstant (B8  x)] = Just $ VConstant (B32 (fromIntegral (fromIntegral x :: Int8)))
sext IT8  IT64 [VConstant (B8  x)] = Just $ VConstant (B64 (fromIntegral (fromIntegral x :: Int8)))
sext IT16 IT32 [VConstant (B16 x)] = Just $ VConstant (B32 (fromIntegral (fromIntegral x :: Int16)))
sext IT16 IT64 [VConstant (B16 x)] = Just $ VConstant (B64 (fromIntegral (fromIntegral x :: Int16)))
sext IT32 IT64 [VConstant (B32 x)] = Just $ VConstant (B64 (fromIntegral (fromIntegral x :: Int32)))
sext _ _ _ = Nothing

trunc IT16 IT8  [VConstant (B16 x)] = Just $ VConstant (B8  (fromIntegral x))
trunc IT32 IT8  [VConstant (B32 x)] = Just $ VConstant (B8  (fromIntegral x))
trunc IT64 IT8  [VConstant (B64 x)] = Just $ VConstant (B8  (fromIntegral x))
trunc IT32 IT16 [VConstant (B32 x)] = Just $ VConstant (B16 (fromIntegral x))
trunc IT64 IT16 [VConstant (B64 x)] = Just $ VConstant (B16 (fromIntegral x))
trunc IT64 IT32 [VConstant (B64 x)] = Just $ VConstant (B32 (fromIntegral x))
trunc _ _ _ = Nothing

intToBits8  [VConstant (I x)] = Just $ toB IT8 x
intToBits8 _ = Nothing
intToBits16 [VConstant (I x)] = Just $ toB IT16 x
intToBits16 _ = Nothing
intToBits32  [VConstant (I x)] = Just $ toB IT32 x
intToBits32 _ = Nothing
intToBits64 [VConstant (I x)] = Just $ toB IT64 x
intToBits64 _ = Nothing

bits32ToInt [VConstant (B32 x)] = Just $ VConstant (I (fromIntegral x))
bits32ToInt _ = Nothing

c_intToStr [VConstant (I x)] = Just $ VConstant (Str (show x))
c_intToStr _ = Nothing
c_strToInt [VConstant (Str x)] = case reads x of
                                    [(n,"")] -> Just $ VConstant (I n)
                                    _ -> Just $ VConstant (I 0)
c_strToInt _ = Nothing

c_intToChar [VConstant (I x)] = Just $ VConstant (Ch (toEnum x))
c_intToChar _ = Nothing
c_charToInt [VConstant (Ch x)] = Just $ VConstant (I (fromEnum x))
c_charToInt _ = Nothing

c_intToBigInt [VConstant (I x)] = Just $ VConstant (BI (fromIntegral x))
c_intToBigInt _ = Nothing
c_bigIntToInt [VConstant (BI x)] = Just $ VConstant (I (fromInteger x))
c_bigIntToInt _ = Nothing

c_bigIntToStr [VConstant (BI x)] = Just $ VConstant (Str (show x))
c_bigIntToStr _ = Nothing
c_strToBigInt [VConstant (Str x)] = case reads x of
                                        [(n,"")] -> Just $ VConstant (BI n)
                                        _ -> Just $ VConstant (BI 0)
c_strToBigInt _ = Nothing

c_floatToStr [VConstant (Fl x)] = Just $ VConstant (Str (show x))
c_floatToStr _ = Nothing
c_strToFloat [VConstant (Str x)] = case reads x of
                                        [(n,"")] -> Just $ VConstant (Fl n)
                                        _ -> Just $ VConstant (Fl 0)
c_strToFloat _ = Nothing

c_floatToInt [VConstant (Fl x)] = Just $ VConstant (I (truncate x))
c_floatToInt _ = Nothing

c_intToFloat [VConstant (I x)] = Just $ VConstant (Fl (fromIntegral x))
c_intToFloat _ = Nothing

p_fPrim f [VConstant (Fl x)] = Just $ VConstant (Fl (f x))
p_fPrim f _ = Nothing

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

p_strLen [VConstant (Str xs)] = Just $ VConstant (I (length xs))
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


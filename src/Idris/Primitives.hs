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
    (2, LPlus) total,
   Prim (UN "prim__subInt") (ty [IType, IType] IType) 2 (iBin (-))
     (2, LMinus) total,
   Prim (UN "prim__mulInt") (ty [IType, IType] IType) 2 (iBin (*))
     (2, LTimes) total,
   Prim (UN "prim__divInt") (ty [IType, IType] IType) 2 (iBin div)
     (2, LDiv) partial,
   Prim (UN "prim__modInt") (ty [IType, IType] IType) 2 (iBin mod)
     (2, LMod) partial,
   Prim (UN "prim__andInt") (ty [IType, IType] IType) 2 (iBin (.&.))
     (2, LAnd) partial,
   Prim (UN "prim__orInt") (ty [IType, IType] IType) 2 (iBin (.|.))
     (2, LOr) partial,
   Prim (UN "prim__xorInt") (ty [IType, IType] IType) 2 (iBin xor)
     (2, LXOr) partial,
   Prim (UN "prim__shLInt") (ty [IType, IType] IType) 2 (iBin shiftL)
     (2, LSHL) partial,
   Prim (UN "prim__shRInt") (ty [IType, IType] IType) 2 (iBin shiftR)
     (2, LSHR) partial,
   Prim (UN "prim__complInt") (ty [IType] IType) 1 (iUn complement)
     (1, LCompl) partial,
   Prim (UN "prim__eqInt")  (ty [IType, IType] IType) 2 (biBin (==))
     (2, LEq) total,
   Prim (UN "prim__ltInt")  (ty [IType, IType] IType) 2 (biBin (<))
     (2, LLt) total,
   Prim (UN "prim__lteInt") (ty [IType, IType] IType) 2 (biBin (<=))
     (2, LLe) total,
   Prim (UN "prim__gtInt")  (ty [IType, IType] IType) 2 (biBin (>))
     (2, LGt) total,
   Prim (UN "prim__gteInt") (ty [IType, IType] IType) 2 (biBin (>=))
     (2, LGe) total,
   Prim (UN "prim__eqChar")  (ty [ChType, ChType] IType) 2 (bcBin (==))
     (2, LEq) total,
   Prim (UN "prim__ltChar")  (ty [ChType, ChType] IType) 2 (bcBin (<))
     (2, LLt) total,
   Prim (UN "prim__lteChar") (ty [ChType, ChType] IType) 2 (bcBin (<=))
     (2, LLe) total,
   Prim (UN "prim__gtChar")  (ty [ChType, ChType] IType) 2 (bcBin (>))
     (2, LGt) total,
   Prim (UN "prim__gteChar") (ty [ChType, ChType] IType) 2 (bcBin (>=))
     (2, LGe) total,

   Prim (UN "prim__ltB8") (ty [B8Type, B8Type] IType) 2 (b8Cmp (<))
     (2, LB8Lt) total,
   Prim (UN "prim__lteB8") (ty [B8Type, B8Type] IType) 2 (b8Cmp (<=))
     (2, LB8Lte) total,
   Prim (UN "prim__eqB8") (ty [B8Type, B8Type] IType) 2 (b8Cmp (==))
     (2, LB8Eq) total,
   Prim (UN "prim__gteB8") (ty [B8Type, B8Type] IType) 2 (b8Cmp (>))
     (2, LB8Gte) total,
   Prim (UN "prim__gtB8") (ty [B8Type, B8Type] IType) 2 (b8Cmp (>=))
     (2, LB8Gt) total,
   Prim (UN "prim__addB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin (+))
     (2, LB8Plus) total,
   Prim (UN "prim__subB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin (-))
     (2, LB8Minus) total,
   Prim (UN "prim__mulB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin (*))
     (2, LB8Times) total,
   Prim (UN "prim__udivB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin div)
     (2, LB8UDiv) partial,
   Prim (UN "prim__sdivB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin s8div)
     (2, LB8SDiv) partial,
   Prim (UN "prim__uremB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin rem)
     (2, LB8URem) partial,
   Prim (UN "prim__sremB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin s8rem)
     (2, LB8SRem) partial,
   Prim (UN "prim__shlB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin (\x y -> shiftL x (fromIntegral y)))
     (2, LB8Shl) total,
   Prim (UN "prim__lshrB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin (\x y -> shiftR x (fromIntegral y)))
     (2, LB8AShr) total,
   Prim (UN "prim__ashrB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin (\x y -> fromIntegral $
                                                                           shiftR (fromIntegral x :: Int8)
                                                                                  (fromIntegral y)))
     (2, LB8LShr) total,
   Prim (UN "prim__andB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin (.&.))
     (2, LB8And) total,
   Prim (UN "prim__orB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin (.|.))
     (2, LB8Or) total,
   Prim (UN "prim__xorB8") (ty [B8Type, B8Type] B8Type) 2 (b8Bin xor)
     (2, LB8Xor) total,
   Prim (UN "prim__complB8") (ty [B8Type] B8Type) 1 (b8Un complement)
     (1, LB8Compl) total,
   Prim (UN "prim__zextB8_16") (ty [B8Type] B16Type) 1 zext8_16
     (1, LB8Z16) total,
   Prim (UN "prim__zextB8_32") (ty [B8Type] B32Type) 1 zext8_32
     (1, LB8Z32) total,
   Prim (UN "prim__zextB8_64") (ty [B8Type] B64Type) 1 zext8_64
     (1, LB8Z64) total,
   Prim (UN "prim__sextB8_16") (ty [B8Type] B16Type) 1 sext8_16
     (1, LB8Z16) total,
   Prim (UN "prim__sextB8_32") (ty [B8Type] B32Type) 1 sext8_32
     (1, LB8Z32) total,
   Prim (UN "prim__sextB8_64") (ty [B8Type] B64Type) 1 sext8_64
     (1, LB8Z64) total,

   Prim (UN "prim__ltB16") (ty [B16Type, B16Type] IType) 2 (b16Cmp (<))
     (2, LB16Lt) total,
   Prim (UN "prim__lteB16") (ty [B16Type, B16Type] IType) 2 (b16Cmp (<=))
     (2, LB16Lte) total,
   Prim (UN "prim__eqB16") (ty [B16Type, B16Type] IType) 2 (b16Cmp (==))
     (2, LB16Eq) total,
   Prim (UN "prim__gteB16") (ty [B16Type, B16Type] IType) 2 (b16Cmp (>))
     (2, LB16Gte) total,
   Prim (UN "prim__gtB16") (ty [B16Type, B16Type] IType) 2 (b16Cmp (>=))
     (2, LB16Gt) total,
   Prim (UN "prim__addB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin (+))
     (2, LB16Plus) total,
   Prim (UN "prim__subB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin (-))
     (2, LB16Minus) total,
   Prim (UN "prim__mulB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin (*))
     (2, LB16Times) total,
   Prim (UN "prim__udivB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin div)
     (2, LB16UDiv) partial,
   Prim (UN "prim__sdivB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin s16div)
     (2, LB16SDiv) partial,
   Prim (UN "prim__uremB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin rem)
     (2, LB16URem) partial,
   Prim (UN "prim__sremB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin s16rem)
     (2, LB16SRem) partial,
   Prim (UN "prim__shlB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin (\x y -> shiftL x (fromIntegral y)))
     (2, LB16Shl) total,
   Prim (UN "prim__lshrB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin (\x y -> shiftR x (fromIntegral y)))
     (2, LB16AShr) total,
   Prim (UN "prim__ashrB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin (\x y -> fromIntegral $
                                                                                shiftR (fromIntegral x :: Int16)
                                                                                       (fromIntegral y)))
     (2, LB16LShr) total,
   Prim (UN "prim__andB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin (.&.))
     (2, LB16And) total,
   Prim (UN "prim__orB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin (.|.))
     (2, LB16Or) total,
   Prim (UN "prim__xorB16") (ty [B16Type, B16Type] B16Type) 2 (b16Bin xor)
     (2, LB16Xor) total,
   Prim (UN "prim__complB16") (ty [B16Type] B16Type) 1 (b16Un complement)
     (1, LB16Compl) total,
   Prim (UN "prim__zextB16_32") (ty [B16Type] B32Type) 1 zext16_32
     (1, LB16Z32) total,
   Prim (UN "prim__zextB16_64") (ty [B16Type] B64Type) 1 zext16_64
     (1, LB16Z64) total,
   Prim (UN "prim__sextB16_32") (ty [B16Type] B32Type) 1 sext16_32
     (1, LB16Z32) total,
   Prim (UN "prim__sextB16_64") (ty [B16Type] B64Type) 1 sext16_64
     (1, LB16Z64) total,
   Prim (UN "prim__truncB16_8") (ty [B16Type] B8Type) 1 trunc16_8
     (1, LB16T8) total,

   Prim (UN "prim__ltB32") (ty [B32Type, B32Type] IType) 2 (b32Cmp (<))
     (2, LB32Lt) total,
   Prim (UN "prim__lteB32") (ty [B32Type, B32Type] IType) 2 (b32Cmp (<=))
     (2, LB32Lte) total,
   Prim (UN "prim__eqB32") (ty [B32Type, B32Type] IType) 2 (b32Cmp (==))
     (2, LB32Eq) total,
   Prim (UN "prim__gteB32") (ty [B32Type, B32Type] IType) 2 (b32Cmp (>))
     (2, LB32Gte) total,
   Prim (UN "prim__gtB32") (ty [B32Type, B32Type] IType) 2 (b32Cmp (>=))
     (2, LB32Gt) total,
   Prim (UN "prim__addB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin (+))
     (2, LB32Plus) total,
   Prim (UN "prim__subB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin (-))
     (2, LB32Minus) total,
   Prim (UN "prim__mulB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin (*))
     (2, LB32Times) total,
   Prim (UN "prim__udivB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin div)
     (2, LB32UDiv) partial,
   Prim (UN "prim__sdivB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin s32div)
     (2, LB32SDiv) partial,
   Prim (UN "prim__uremB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin rem)
     (2, LB32URem) partial,
   Prim (UN "prim__sremB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin s32rem)
     (2, LB32SRem) partial,
   Prim (UN "prim__shlB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin (\x y -> shiftL x (fromIntegral y)))
     (2, LB32Shl) total,
   Prim (UN "prim__lshrB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin (\x y -> shiftR x (fromIntegral y)))
     (2, LB32AShr) total,
   Prim (UN "prim__ashrB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin (\x y -> fromIntegral $
                                                                                shiftR (fromIntegral x :: Int32)
                                                                                       (fromIntegral y)))
     (2, LB32LShr) total,
   Prim (UN "prim__andB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin (.&.))
     (2, LB32And) total,
   Prim (UN "prim__orB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin (.|.))
     (2, LB32Or) total,
   Prim (UN "prim__xorB32") (ty [B32Type, B32Type] B32Type) 2 (b32Bin xor)
     (2, LB32Xor) total,
   Prim (UN "prim__complB32") (ty [B32Type] B32Type) 1 (b32Un complement)
     (1, LB32Compl) total,
   Prim (UN "prim__zextB32_64") (ty [B32Type] B64Type) 1 zext32_64
     (1, LB32Z64) total,
   Prim (UN "prim__sextB32_64") (ty [B32Type] B64Type) 1 sext32_64
     (1, LB32Z64) total,
   Prim (UN "prim__truncB32_8") (ty [B32Type] B8Type) 1 trunc32_8
     (1, LB32T8) total,
   Prim (UN "prim__truncB32_16") (ty [B32Type] B16Type) 1 trunc32_16
     (1, LB32T16) total,

   Prim (UN "prim__ltB64") (ty [B64Type, B64Type] IType) 2 (b64Cmp (<))
     (2, LB64Lt) total,
   Prim (UN "prim__lteB64") (ty [B64Type, B64Type] IType) 2 (b64Cmp (<=))
     (2, LB64Lte) total,
   Prim (UN "prim__eqB64") (ty [B64Type, B64Type] IType) 2 (b64Cmp (==))
     (2, LB64Eq) total,
   Prim (UN "prim__gteB64") (ty [B64Type, B64Type] IType) 2 (b64Cmp (>))
     (2, LB64Gte) total,
   Prim (UN "prim__gtB64") (ty [B64Type, B64Type] IType) 2 (b64Cmp (>=))
     (2, LB64Gt) total,
   Prim (UN "prim__addB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin (+))
     (2, LB64Plus) total,
   Prim (UN "prim__subB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin (-))
     (2, LB64Minus) total,
   Prim (UN "prim__mulB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin (*))
     (2, LB64Times) total,
   Prim (UN "prim__udivB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin div)
     (2, LB64UDiv) partial,
   Prim (UN "prim__sdivB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin s64div)
     (2, LB64SDiv) partial,
   Prim (UN "prim__uremB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin rem)
     (2, LB64URem) partial,
   Prim (UN "prim__sremB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin s64rem)
     (2, LB64SRem) partial,
   Prim (UN "prim__shlB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin (\x y -> shiftL x (fromIntegral y)))
     (2, LB64Shl) total,
   Prim (UN "prim__lshrB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin (\x y -> shiftR x (fromIntegral y)))
     (2, LB64AShr) total,
   Prim (UN "prim__ashrB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin (\x y -> fromIntegral $
                                                                                shiftR (fromIntegral x :: Int64)
                                                                                       (fromIntegral y)))
     (2, LB64LShr) total,
   Prim (UN "prim__andB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin (.&.))
     (2, LB64And) total,
   Prim (UN "prim__orB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin (.|.))
     (2, LB64Or) total,
   Prim (UN "prim__xorB64") (ty [B64Type, B64Type] B64Type) 2 (b64Bin xor)
     (2, LB64Xor) total,
   Prim (UN "prim__complB64") (ty [B64Type] B64Type) 1 (b64Un complement)
     (1, LB64Compl) total,
   Prim (UN "prim__truncB64_8") (ty [B64Type] B8Type) 1 trunc64_8
     (1, LB64T8) total,
   Prim (UN "prim__truncB64_16") (ty [B64Type] B16Type) 1 trunc64_16
     (1, LB64T16) total,
   Prim (UN "prim__truncB64_32") (ty [B64Type] B32Type) 1 trunc64_32
     (1, LB64T32) total,

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
  ]

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

s8div :: Word8 -> Word8 -> Word8
s8div x y = fromIntegral (fromIntegral x `div` fromIntegral y :: Int8)

s16div :: Word16 -> Word16 -> Word16
s16div x y = fromIntegral (fromIntegral x `div` fromIntegral y :: Int16)

s32div :: Word32 -> Word32 -> Word32
s32div x y = fromIntegral (fromIntegral x `div` fromIntegral y :: Int32)

s64div :: Word64 -> Word64 -> Word64
s64div x y = fromIntegral (fromIntegral x `div` fromIntegral y :: Int64)

s8rem :: Word8 -> Word8 -> Word8
s8rem x y = fromIntegral (fromIntegral x `rem` fromIntegral y :: Int8)

s16rem :: Word16 -> Word16 -> Word16
s16rem x y = fromIntegral (fromIntegral x `rem` fromIntegral y :: Int16)

s32rem :: Word32 -> Word32 -> Word32
s32rem x y = fromIntegral (fromIntegral x `rem` fromIntegral y :: Int32)

s64rem :: Word64 -> Word64 -> Word64
s64rem x y = fromIntegral (fromIntegral x `rem` fromIntegral y :: Int64)

b8Bin op [VConstant (B8 x), VConstant (B8 y)] = Just $ VConstant (B8 (op x y))
b8Bin _ _ = Nothing

b8Un op [VConstant (B8 x)] = Just $ VConstant (B8 (op x))
b8Un _ _ = Nothing

b16Bin op [VConstant (B16 x), VConstant (B16 y)] = Just $ VConstant (B16 (op x y))
b16Bin _ _ = Nothing

b16Un op [VConstant (B16 x)] = Just $ VConstant (B16 (op x))
b16Un _ _ = Nothing

b32Bin op [VConstant (B32 x), VConstant (B32 y)] = Just $ VConstant (B32 (op x y))
b32Bin _ _ = Nothing

b32Un op [VConstant (B32 x)] = Just $ VConstant (B32 (op x))
b32Un _ _ = Nothing

b64Bin op [VConstant (B64 x), VConstant (B64 y)] = Just $ VConstant (B64 (op x y))
b64Bin _ _ = Nothing

b64Un op [VConstant (B64 x)] = Just $ VConstant (B64 (op x))
b64Un _ _ = Nothing

b8Cmp op [VConstant (B8 x), VConstant (B8 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
b8Cmp _ _ = Nothing

b16Cmp op [VConstant (B16 x), VConstant (B16 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
b16Cmp _ _ = Nothing

b32Cmp op [VConstant (B32 x), VConstant (B32 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
b32Cmp _ _ = Nothing

b64Cmp op [VConstant (B64 x), VConstant (B64 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
b64Cmp _ _ = Nothing

toB8 x = VConstant (B8 (fromIntegral x))
toB16 x = VConstant (B16 (fromIntegral x))
toB32 x = VConstant (B32 (fromIntegral x))
toB64 x = VConstant (B64 (fromIntegral x))

zext8_16 [VConstant (B8 x)] = Just $ toB16 x
zext8_16 _ = Nothing

zext8_32 [VConstant (B8 x)] = Just $ toB32 x
zext8_32 _ = Nothing

zext8_64 [VConstant (B8 x)] = Just $ toB64 x
zext8_64 _ = Nothing

sext8_16 [VConstant (B8 x)] = Just $ toB16 (fromIntegral x :: Int8)
sext8_16 _ = Nothing

sext8_32 [VConstant (B8 x)] = Just $ toB32 (fromIntegral x :: Int8)
sext8_32 _ = Nothing

sext8_64 [VConstant (B8 x)] = Just $ toB64 (fromIntegral x :: Int8)
sext8_64 _ = Nothing

zext16_32 [VConstant (B16 x)] = Just $ toB32 x
zext16_32 _ = Nothing

zext16_64 [VConstant (B16 x)] = Just $ toB64 x
zext16_64 _ = Nothing

sext16_32 [VConstant (B16 x)] = Just $ toB32 (fromIntegral x :: Int16)
sext16_32 _ = Nothing

sext16_64 [VConstant (B16 x)] = Just $ toB64 (fromIntegral x :: Int16)
sext16_64 _ = Nothing

trunc16_8 [VConstant (B16 x)] = Just $ toB8 x
trunc16_8 _ = Nothing

zext32_64 [VConstant (B32 x)] = Just $ toB64 x
zext32_64 _ = Nothing

sext32_64 [VConstant (B32 x)] = Just $ toB64 (fromIntegral x :: Int32)
sext32_64 _ = Nothing

trunc32_8 [VConstant (B32 x)] = Just $ toB8 x
trunc32_8 _ = Nothing

trunc32_16 [VConstant (B32 x)] = Just $ toB16 x
trunc32_16 _ = Nothing

trunc64_8 [VConstant (B64 x)] = Just $ toB8 x
trunc64_8 _ = Nothing

trunc64_16 [VConstant (B64 x)] = Just $ toB16 x
trunc64_16 _ = Nothing

trunc64_32 [VConstant (B64 x)] = Just $ toB32 x
trunc64_32 _ = Nothing

intToBits8  [VConstant (I x)] = Just $ toB8 x
intToBits8 _ = Nothing
intToBits16 [VConstant (I x)] = Just $ toB16 x
intToBits16 _ = Nothing
intToBits32  [VConstant (I x)] = Just $ toB32 x
intToBits32 _ = Nothing
intToBits64 [VConstant (I x)] = Just $ toB64 x
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


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
                   p_def   :: [Const] -> Maybe Const,
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

iCmp, iBinOp, iUnOp :: IntTy -> String -> ([Const] -> Maybe Const) -> (IntTy -> PrimFn) -> Totality -> Prim
iCmp ity op impl irop totality = Prim (UN $ "prim__" ++ op ++ intTyName ity) (ty (replicate 2 $ intTyToConst ity) IType) 2 impl (2, irop ity) totality
iBinOp ity op impl irop totality = Prim (UN $ "prim__" ++ op ++ intTyName ity) (ty (replicate 2 $ intTyToConst ity) (intTyToConst ity)) 2 impl (2, irop ity) totality
iUnOp ity op impl irop totality = Prim (UN $ "prim__" ++ op ++ intTyName ity) (ty [intTyToConst ity] (intTyToConst ity)) 1 impl (1, irop ity) totality

iCoerce :: IntTy -> IntTy -> String -> (IntTy -> IntTy -> [Const] -> Maybe Const) -> (IntTy -> IntTy -> PrimFn) -> Prim
iCoerce from to op impl irop =
    Prim (UN $ "prim__" ++ op ++ intTyName from ++ "_" ++ intTyName to)
             (ty [intTyToConst from] (intTyToConst to)) 1 (impl from to) (1, irop from to) total

p_believeMe :: [a] -> Maybe a
p_believeMe [_,_,x] = Just x
p_believeMe _ = Nothing

iUn :: (Int -> Int) -> [Const] -> Maybe Const
iUn op [I x] = Just $ I (op x)
iUn _ _ = Nothing

iBin :: (Int -> Int -> Int) -> [Const] -> Maybe Const
iBin op [I x, I y] = Just $ I (op x y)
iBin _ _ = Nothing

bBin :: (Integer -> Integer -> Integer) -> [Const] -> Maybe Const
bBin op [BI x, BI y] = Just $ BI (op x y)
bBin _ _ = Nothing

bBini :: (Integer -> Integer -> Int) -> [Const] -> Maybe Const
bBini op [BI x, BI y] = Just $ I (op x y)
bBini _ _ = Nothing

biBin :: (Int -> Int -> Bool) -> [Const] -> Maybe Const
biBin op = iBin (\x y -> if (op x y) then 1 else 0)

bbBin :: (Integer -> Integer -> Bool) -> [Const] -> Maybe Const
bbBin op = bBini (\x y -> if (op x y) then 1 else 0)

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
bsrem IT8 [B8 x, B8 y]
    = Just $ B8 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int8))
bsrem IT16 [B16 x, B16 y]
    = Just $ B16 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int16))
bsrem IT32 [B32 x, B32 y]
    = Just $ B32 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int32))
bsrem IT64 [B64 x, B64 y]
    = Just $ B64 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int64))
bsrem ITNative [I x, I y] = Just $ I (x `rem` y)
bsrem _ _ = Nothing

bsdiv :: IntTy -> [Const] -> Maybe Const
bsdiv IT8 [B8 x, B8 y]
    = Just $ B8 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int8))
bsdiv IT16 [B16 x, B16 y]
    = Just $ B16 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int16))
bsdiv IT32 [B32 x, B32 y]
    = Just $ B32 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int32))
bsdiv IT64 [B64 x, B64 y]
    = Just $ B64 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int64))
bsdiv ITNative [I x, I y] = Just $ I (x `div` y)
bsdiv _ _ = Nothing

bashr :: IntTy -> [Const] -> Maybe Const
bashr IT8 [B8 x, B8 y]
    = Just $ B8 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int8))
bashr IT16 [B16 x, B16 y]
    = Just $ B16 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int16))
bashr IT32 [B32 x, B32 y]
    = Just $ B32 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int32))
bashr IT64 [B64 x, B64 y]
    = Just $ B64 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int64))
bashr ITNative [I x, I y] = Just $ I (x `shiftR` y)
bashr _ _ = Nothing

bUn :: IntTy -> (forall a. Bits a => a -> a) -> [Const] -> Maybe Const
bUn IT8      op [B8  x] = Just $ B8  (op x)
bUn IT16     op [B16 x] = Just $ B16 (op x)
bUn IT32     op [B32 x] = Just $ B32 (op x)
bUn IT64     op [B64 x] = Just $ B64 (op x)
bUn ITBig    op [BI x]  = Just $ BI (op x)
bUn ITNative op [I x]   = Just $ I (op x)
bUn _        _   _      = Nothing

bitBin :: IntTy -> (forall a. (Bits a, Integral a) => a -> a -> a) -> [Const] -> Maybe Const
bitBin IT8      op [B8  x, B8  y] = Just $ B8  (op x y)
bitBin IT16     op [B16 x, B16 y] = Just $ B16 (op x y)
bitBin IT32     op [B32 x, B32 y] = Just $ B32 (op x y)
bitBin IT64     op [B64 x, B64 y] = Just $ B64 (op x y)
bitBin ITBig    op [BI x,  BI y]  = Just $ BI (op x y)
bitBin ITNative op [I x,   I y]   = Just $ I (op x y)
bitBin _        _  _              = Nothing

bCmp :: IntTy -> (forall a. Ord a => a -> a -> Bool) -> [Const] -> Maybe Const
bCmp IT8      op [B8  x, B8  y] = Just $ I (if (op x y) then 1 else 0)
bCmp IT16     op [B16 x, B16 y] = Just $ I (if (op x y) then 1 else 0)
bCmp IT32     op [B32 x, B32 y] = Just $ I (if (op x y) then 1 else 0)
bCmp IT64     op [B64 x, B64 y] = Just $ I (if (op x y) then 1 else 0)
bCmp ITBig    op [BI x, BI y]   = Just $ I (if (op x y) then 1 else 0)
bCmp ITNative op [I x, I y]     = Just $ I (if (op x y) then 1 else 0)
bCmp _        _  _              = Nothing

toInt :: Integral a => IntTy -> a -> Const
toInt IT8      x = B8 (fromIntegral x)
toInt IT16     x = B16 (fromIntegral x)
toInt IT32     x = B32 (fromIntegral x)
toInt IT64     x = B64 (fromIntegral x)
toInt ITBig    x = BI (fromIntegral x)
toInt ITNative x = I (fromIntegral x)

intToInt :: IntTy -> IntTy -> [Const] -> Maybe Const
intToInt IT8      out [B8 x]  = Just $ toInt out x
intToInt IT16     out [B16 x] = Just $ toInt out x
intToInt IT32     out [B32 x] = Just $ toInt out x
intToInt IT64     out [B64 x] = Just $ toInt out x
intToInt ITBig    out [BI x]  = Just $ toInt out x
intToInt ITNative out [I x]   = Just $ toInt out x
intToInt _ _ _ = Nothing

zext :: IntTy -> IntTy -> [Const] -> Maybe Const
zext from ITBig val = intToInt from ITBig val
zext ITBig _ _ = Nothing
zext from to val
    | intTyWidth from < intTyWidth to = intToInt from to val
zext _ _ _ = Nothing

sext :: IntTy -> IntTy -> [Const] -> Maybe Const
sext IT8  out [B8  x] = Just $ toInt out (fromIntegral x :: Int8)
sext IT16 out [B16 x] = Just $ toInt out (fromIntegral x :: Int16)
sext IT32 out [B32 x] = Just $ toInt out (fromIntegral x :: Int32)
sext IT64 out [B64 x] = Just $ toInt out (fromIntegral x :: Int64)
sext ITBig _  _       = Nothing
sext from to  val     = intToInt from to val

trunc :: IntTy -> IntTy -> [Const] -> Maybe Const
trunc ITBig to val = intToInt ITBig to val
trunc _ ITBig _ = Nothing
trunc from to val | intTyWidth from > intTyWidth to = intToInt from to val
trunc _ _ _ = Nothing

getInt :: [Const] -> Maybe Integer
getInt [B8 x]  = Just . toInteger $ x
getInt [B16 x] = Just . toInteger $ x
getInt [B32 x] = Just . toInteger $ x
getInt [B64 x] = Just . toInteger $ x
getInt [I x]   = Just . toInteger $ x
getInt [BI x]  = Just x
getInt _       = Nothing

intToStr :: [Const] -> Maybe Const
intToStr val | Just i <- getInt val = Just $ Str (show i)
intToStr _ = Nothing

strToInt :: IntTy -> [Const] -> Maybe Const
strToInt ity [Str x] = case reads x of
                         [(n,"")] -> Just $ toInt ity (n :: Integer)
                         _        -> Just $ I 0
strToInt _ _ = Nothing

intToFloat :: [Const] -> Maybe Const
intToFloat val | Just i <- getInt val = Just $ Fl (fromIntegral i)
intToFloat _ = Nothing

floatToInt :: IntTy -> [Const] -> Maybe Const
floatToInt ity [Fl x] = Just $ toInt ity (truncate x :: Integer)
floatToInt _ _ = Nothing

c_intToChar, c_charToInt :: [Const] -> Maybe Const
c_intToChar [(I x)] = Just . Ch . toEnum $ x
c_intToChar _ = Nothing
c_charToInt [(Ch x)] = Just . I . fromEnum $ x
c_charToInt _ = Nothing

c_floatToStr :: [Const] -> Maybe Const
c_floatToStr [Fl x] = Just $ Str (show x)
c_floatToStr _ = Nothing
c_strToFloat [Str x] = case reads x of
                         [(n,"")] -> Just $ Fl n
                         _ -> Just $ Fl 0
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

p_strLen, p_strHead, p_strTail, p_strIndex, p_strCons, p_strRev :: [Const] -> Maybe Const
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

p_cantreduce :: a -> Maybe b
p_cantreduce _ = Nothing

valuePrim :: ([Const] -> Maybe Const) -> [Value] -> Maybe Value
valuePrim prim vals = fmap VConstant (mapM getConst vals >>= prim)
    where getConst (VConstant c) = Just c
          getConst _             = Nothing

elabPrim :: Prim -> Idris ()
elabPrim (Prim n ty i def sc tot)
    = do updateContext (addOperator n ty i (valuePrim def))
         setTotality n tot
         i <- getIState
         putIState i { idris_scprims = (n, sc) : idris_scprims i }

elabPrims :: Idris ()
elabPrims = do mapM_ (elabDecl EAll toplevel)
                     (map (PData "" defaultSyntax (FC "builtin" 0) False)
                         [inferDecl, unitDecl, falseDecl, pairDecl, eqDecl])
               mapM_ elabPrim primitives


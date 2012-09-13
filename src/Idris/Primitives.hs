{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module Idris.Primitives(elabPrims) where

import Idris.ElabDecls
import Idris.ElabTerm
import Idris.AbsSyntax

import IRTS.Lang

import Core.TT
import Core.Evaluate

import Epic.Epic hiding (Term, Type, Name, fn)
import qualified Epic.Epic as E

data Prim = Prim { p_name  :: Name,
                   p_type  :: Type,
                   p_arity :: Int,
                   p_def   :: [Value] -> Maybe Value,
                   p_epic  :: ([E.Name], E.Term),
		   p_lexp  :: (Int, PrimFn),
                   p_total :: Totality
                 }

ty []     x = Constant x
ty (t:ts) x = Bind (MN 0 "T") (Pi (Constant t)) (ty ts x)

believeTy = Bind (UN "a") (Pi (Set (UVar (-2))))
            (Bind (UN "b") (Pi (Set (UVar (-2))))
            (Bind (UN "x") (Pi (V 1)) (V 1)))

type ETm = E.Term
type EOp = E.Op

fun = E.fn
ref = E.ref

eOp :: EOp -> ([E.Name], ETm)
eOp op = ([E.name "x", E.name "y"], E.op_ op (E.fn "x") (E.fn "y")) 

eOpFn :: E.Type -> E.Type -> String -> ([E.Name], ETm)
eOpFn ty rty op = ([E.name "x", E.name "y"], 
                    foreign_ rty op [(E.fn "x", ty), (E.fn "y", ty)])

strToInt x = foreign_ tyInt "strToInt" [(x, tyString)]
intToStr x = foreign_ tyString "intToStr" [(x, tyInt)]
charToInt x = x
intToChar x = x
intToBigInt x = foreign_ tyBigInt "intToBigInt" [(x, tyInt)]
bigIntToInt x = foreign_ tyInt "bigIntToInt" [(x, tyBigInt)]
strToBigInt x = foreign_ tyBigInt "strToBig" [(x, tyString)]
bigIntToStr x = foreign_ tyString "bigToStr" [(x, tyBigInt)]
strToFloat x = foreign_ tyFloat "strToFloat" [(x, tyString)]
floatToStr x = foreign_ tyString "floatToStr" [(x, tyFloat)]
intToFloat x = foreign_ tyFloat "intToFloat" [(x, tyInt)]
floatToInt x = foreign_ tyInt "floatToInt" [(x, tyFloat)]

floatExp x = foreign_ tyFloat "exp" [(x, tyFloat)]
floatLog x = foreign_ tyFloat "log" [(x, tyFloat)]
floatSin x = foreign_ tyFloat "sin" [(x, tyFloat)]
floatCos x = foreign_ tyFloat "cos" [(x, tyFloat)]
floatTan x = foreign_ tyFloat "tan" [(x, tyFloat)]
floatASin x = foreign_ tyFloat "asin" [(x, tyFloat)]
floatACos x = foreign_ tyFloat "acos" [(x, tyFloat)]
floatATan x = foreign_ tyFloat "atan" [(x, tyFloat)]
floatFloor x = foreign_ tyFloat "floor" [(x, tyFloat)]
floatCeil x = foreign_ tyFloat "ceil" [(x, tyFloat)]
floatSqrt x = foreign_ tyFloat "sqrt" [(x, tyFloat)]

strIndex x i = foreign_ tyChar "strIndex" [(x, tyString), (i, tyInt)]
strHead x = foreign_ tyChar "strHead" [(x, tyString)]
strTail x = foreign_ tyString "strTail" [(x, tyString)]
strCons x xs = foreign_ tyString "strCons" [(x, tyChar), (xs, tyString)]
strRev x = foreign_ tyString "strrev" [(x, tyString)]
strEq x y = foreign_ tyInt "streq" [(x, tyString), (y, tyString)]
strLt x y = foreign_ tyInt "strlt" [(x, tyString), (y, tyString)]

readStr x = foreign_ tyString "freadStr" [(x, tyPtr)]

stream_stdin = let args :: [(ETm, E.Type)] = [] in
                   foreign_ tyPtr "get_stdin" args

total = Total []
partial = Partial NotCovering 

primitives =
   -- operators
  [Prim (UN "prim__addInt") (ty [IType, IType] IType) 2 (iBin (+))
   (eOp E.plus_) (2, LPlus) total,
   Prim (UN "prim__subInt") (ty [IType, IType] IType) 2 (iBin (-))
    (eOp E.minus_) 
    (2, LMinus) total,
   Prim (UN "prim__mulInt") (ty [IType, IType] IType) 2 (iBin (*))
    (eOp E.times_) (2, LTimes) total,
   Prim (UN "prim__divInt") (ty [IType, IType] IType) 2 (iBin (div))
    (eOp E.divide_) (2, LDiv) partial,
   Prim (UN "prim__eqInt")  (ty [IType, IType] IType) 2 (biBin (==))
    (eOp E.eq_) (2, LEq) total,
   Prim (UN "prim__ltInt")  (ty [IType, IType] IType) 2 (biBin (<))
    (eOp E.lt_) (2, LLt) total,
   Prim (UN "prim__lteInt") (ty [IType, IType] IType) 2 (biBin (<=))
    (eOp E.lte_) (2, LLe) total,
   Prim (UN "prim__gtInt")  (ty [IType, IType] IType) 2 (biBin (>))
    (eOp E.gt_) (2, LGt) total,
   Prim (UN "prim__gteInt") (ty [IType, IType] IType) 2 (biBin (>=))
    (eOp E.gte_) (2, LGe) total,
   Prim (UN "prim__eqChar")  (ty [ChType, ChType] IType) 2 (bcBin (==))
    (eOp E.eq_) (2, LEq) total,
   Prim (UN "prim__ltChar")  (ty [ChType, ChType] IType) 2 (bcBin (<))
    (eOp E.lt_) (2, LLt) total,
   Prim (UN "prim__lteChar") (ty [ChType, ChType] IType) 2 (bcBin (<=))
    (eOp E.lte_) (2, LLe) total,
   Prim (UN "prim__gtChar")  (ty [ChType, ChType] IType) 2 (bcBin (>))
    (eOp E.gt_) (2, LGt) total,
   Prim (UN "prim__gteChar") (ty [ChType, ChType] IType) 2 (bcBin (>=))
    (eOp E.gte_) (2, LGe) total,
   Prim (UN "prim__addBigInt") (ty [BIType, BIType] BIType) 2 (bBin (+))
    (eOpFn tyBigInt tyBigInt "addBig") 
    (2, LBPlus) total,
   Prim (UN "prim__subBigInt") (ty [BIType, BIType] BIType) 2 (bBin (-))
    (eOpFn tyBigInt tyBigInt "subBig") (2, LBMinus) total,
   Prim (UN "prim__mulBigInt") (ty [BIType, BIType] BIType) 2 (bBin (*))
    (eOpFn tyBigInt tyBigInt "mulBig") (2, LBTimes) total,
   Prim (UN "prim__divBigInt") (ty [BIType, BIType] BIType) 2 (bBin (div))
    (eOpFn tyBigInt tyBigInt "divBig") (2, LBDiv) partial,
   Prim (UN "prim__eqBigInt")  (ty [BIType, BIType] IType) 2 (bbBin (==))
    (eOpFn tyBigInt tyInt "eqBig") (2, LBEq) total,
   Prim (UN "prim__ltBigInt")  (ty [BIType, BIType] IType) 2 (bbBin (<))
    (eOpFn tyBigInt tyInt "ltBig") (2, LBLt) total,
   Prim (UN "prim__lteBigInt")  (ty [BIType, BIType] IType) 2 (bbBin (<=))
    (eOpFn tyBigInt tyInt "leBig") (2, LBLe) total,
   Prim (UN "prim__gtBigInt")  (ty [BIType, BIType] IType) 2 (bbBin (>))
    (eOpFn tyBigInt tyInt "gtBig") (2, LBGt) total,
   Prim (UN "prim__gtBigInt")  (ty [BIType, BIType] IType) 2 (bbBin (>=))
    (eOpFn tyBigInt tyInt "geBig") (2, LBGe) total,
   Prim (UN "prim__addFloat") (ty [FlType, FlType] FlType) 2 (fBin (+))
    (eOp E.plusF_) (2, LFPlus) total,
   Prim (UN "prim__subFloat") (ty [FlType, FlType] FlType) 2 (fBin (-))
    (eOp E.minusF_) (2, LFMinus) total,
   Prim (UN "prim__mulFloat") (ty [FlType, FlType] FlType) 2 (fBin (*))
    (eOp E.timesF_) (2, LFTimes) total,
   Prim (UN "prim__divFloat") (ty [FlType, FlType] FlType) 2 (fBin (/))
    (eOp E.divideF_) (2, LFDiv) total,
   Prim (UN "prim__eqFloat")  (ty [FlType, FlType] IType) 2 (bfBin (==))
    (eOp E.eqF_) (2, LFEq) total,
   Prim (UN "prim__ltFloat")  (ty [FlType, FlType] IType) 2 (bfBin (<))
    (eOp E.ltF_) (2, LFLt) total,
   Prim (UN "prim__lteFloat") (ty [FlType, FlType] IType) 2 (bfBin (<=))
    (eOp E.lteF_) (2, LFLe) total,
   Prim (UN "prim__gtFloat")  (ty [FlType, FlType] IType) 2 (bfBin (>))
    (eOp E.gtF_) (2, LFGt) total,
   Prim (UN "prim__gteFloat") (ty [FlType, FlType] IType) 2 (bfBin (>=))
    (eOp E.gteF_) (2, LFGe) total,
   Prim (UN "prim__concat") (ty [StrType, StrType] StrType) 2 (sBin (++))
    ([E.name "x", E.name "y"], (fun "append") @@ fun "x" @@ fun "y") 
    (2, LStrConcat) total,
   Prim (UN "prim__eqString") (ty [StrType, StrType] IType) 2 (bsBin (==))
    ([E.name "x", E.name "y"], strEq (fun "x") (fun "y")) 
    (2, LStrEq) total,
   Prim (UN "prim__ltString") (ty [StrType, StrType] IType) 2 (bsBin (<))
    ([E.name "x", E.name "y"], strLt (fun "x") (fun "y")) 
    (2, LStrLt) total,
    -- Conversions
   Prim (UN "prim__strToInt") (ty [StrType] IType) 1 (c_strToInt)
    ([E.name "x"], strToInt (fun "x")) (1, LStrInt) total,
   Prim (UN "prim__intToStr") (ty [IType] StrType) 1 (c_intToStr)
    ([E.name "x"], intToStr (fun "x")) (1, LIntStr) total,
   Prim (UN "prim__charToInt") (ty [ChType] IType) 1 (c_charToInt)
    ([E.name "x"], charToInt (fun "x")) (1, LNoOp) total,
   Prim (UN "prim__intToChar") (ty [IType] ChType) 1 (c_intToChar)
    ([E.name "x"], intToChar (fun "x")) (1, LNoOp) total,
   Prim (UN "prim__intToBigInt") (ty [IType] BIType) 1 (c_intToBigInt)
    ([E.name "x"], intToBigInt (fun "x")) (1, LIntBig) total,
   Prim (UN "prim__bigIntToInt") (ty [BIType] IType) 1 (c_bigIntToInt)
    ([E.name "x"], bigIntToInt (fun "x")) (1, LBigInt) total,
   Prim (UN "prim__strToBigInt") (ty [StrType] BIType) 1 (c_strToBigInt)
    ([E.name "x"], strToBigInt (fun "x")) (1, LStrBig) total,
   Prim (UN "prim__bigIntToStr") (ty [BIType] StrType) 1 (c_bigIntToStr)
    ([E.name "x"], bigIntToStr (fun "x")) (1, LBigStr) total,
   Prim (UN "prim__strToFloat") (ty [StrType] FlType) 1 (c_strToFloat)
    ([E.name "x"], strToFloat (fun "x")) (1, LStrFloat) total,
   Prim (UN "prim__floatToStr") (ty [FlType] StrType) 1 (c_floatToStr)
    ([E.name "x"], floatToStr (fun "x")) (1, LFloatStr) total,
   Prim (UN "prim__intToFloat") (ty [IType] FlType) 1 (c_intToFloat)
    ([E.name "x"], intToFloat (fun "x")) (1, LIntFloat) total,
   Prim (UN "prim__floatToInt") (ty [FlType] IType) 1 (c_floatToInt)
    ([E.name "x"], floatToInt (fun "x")) (1, LFloatInt) total,

   Prim (UN "prim__floatExp") (ty [FlType] FlType) 1 (p_floatExp)
    ([E.name "x"], floatExp (fun "x")) (1, LFExp) total, 
   Prim (UN "prim__floatLog") (ty [FlType] FlType) 1 (p_floatLog)
    ([E.name "x"], floatLog (fun "x")) (1, LFLog) total,
   Prim (UN "prim__floatSin") (ty [FlType] FlType) 1 (p_floatSin)
    ([E.name "x"], floatSin (fun "x")) (1, LFSin) total,
   Prim (UN "prim__floatCos") (ty [FlType] FlType) 1 (p_floatCos)
    ([E.name "x"], floatCos (fun "x")) (1, LFCos) total,
   Prim (UN "prim__floatTan") (ty [FlType] FlType) 1 (p_floatTan)
    ([E.name "x"], floatTan (fun "x")) (1, LFTan) total,
   Prim (UN "prim__floatASin") (ty [FlType] FlType) 1 (p_floatASin)
    ([E.name "x"], floatASin (fun "x")) (1, LFASin) total,
   Prim (UN "prim__floatACos") (ty [FlType] FlType) 1 (p_floatACos)
    ([E.name "x"], floatACos (fun "x")) (1, LFACos) total,
   Prim (UN "prim__floatATan") (ty [FlType] FlType) 1 (p_floatATan)
    ([E.name "x"], floatATan (fun "x")) (1, LFATan) total,
   Prim (UN "prim__floatSqrt") (ty [FlType] FlType) 1 (p_floatSqrt)
    ([E.name "x"], floatSqrt (fun "x")) (1, LFSqrt) total,
   Prim (UN "prim__floatFloor") (ty [FlType] FlType) 1 (p_floatFloor)
    ([E.name "x"], floatFloor (fun "x")) (1, LFFloor) total,
   Prim (UN "prim__floatCeil") (ty [FlType] FlType) 1 (p_floatCeil)
    ([E.name "x"], floatCeil (fun "x")) (1, LFCeil) total,

   Prim (UN "prim__strHead") (ty [StrType] ChType) 1 (p_strHead)
    ([E.name "x"], strHead (fun "x")) (1, LStrHead) partial,
   Prim (UN "prim__strTail") (ty [StrType] StrType) 1 (p_strTail)
    ([E.name "x"], strTail (fun "x")) (1, LStrTail) partial,
   Prim (UN "prim__strCons") (ty [ChType, StrType] StrType) 2 (p_strCons)
    ([E.name "x", E.name "xs"], strCons (fun "x") (fun "xs")) 
    (2, LStrCons) total,
   Prim (UN "prim__strIndex") (ty [StrType, IType] ChType) 2 (p_strIndex)
    ([E.name "x", E.name "i"], strIndex (fun "x") (fun "i")) 
    (2, LStrIndex) partial,
   Prim (UN "prim__strRev") (ty [StrType] StrType) 1 (p_strRev)
    ([E.name "x"], strRev (fun "x")) 
    (1, LStrRev) total,
   Prim (UN "prim__readString") (ty [PtrType] StrType) 1 (p_cantreduce)
    ([E.name "h"], readStr (fun "h")) (1, LReadStr) partial,

   -- Streams
   Prim (UN "prim__stdin") (ty [] PtrType) 0 (p_cantreduce)
   ([], stream_stdin) (0, LStdIn) partial,

   Prim (UN "prim__believe_me") believeTy 3 (p_believeMe)
    ([E.name "a", E.name "b", E.name "x"], fun "x") 
    (1, LNoOp) total -- ahem
  ]

p_believeMe [_,_,x] = Just x
p_believeMe _ = Nothing

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
elabPrim (Prim n ty i def epic sc tot) 
    = do updateContext (addOperator n ty i def)
         setTotality n tot
         i <- getIState
         putIState i { idris_prims = (n, epic) : idris_prims i,
	               idris_scprims = (n, sc) : idris_scprims i }

elabPrims :: Idris ()
elabPrims = do mapM_ (elabDecl toplevel) 
                     (map (PData defaultSyntax (FC "builtin" 0))
                         [inferDecl, unitDecl, falseDecl, pairDecl, eqDecl])
               mapM_ elabPrim primitives


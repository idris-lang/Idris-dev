{-|
Module      : IRTS.JavaScript.PrimOp
Description : The JavaScript primitive operations.

License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE OverloadedStrings, PatternGuards, StandaloneDeriving #-}

module IRTS.JavaScript.PrimOp
  ( PrimF
  , PrimDec
  , JsPrimTy(..)
  , primDB
  , jsPrimCoerce
  ) where

import qualified Data.Map.Strict as Map
import Idris.Core.TT
import IRTS.JavaScript.AST
import IRTS.Lang

data JsPrimTy = PTBool | PTAny deriving (Eq, Ord)

type PrimF = [JsExpr] -> JsExpr
type PrimDec = (Bool, JsPrimTy, PrimF) -- the bool indicates if bigint library is used or not

primDB :: Map.Map PrimFn PrimDec
primDB =
  Map.fromList [
    item (LPlus ATFloat) False PTAny $ binop "+"
  , item (LPlus (ATInt ITChar)) False PTAny $ JsForeign "String.fromCharCode(%0.charCodeAt(0) + %1.charCodeAt(0))"
  , item (LPlus (ATInt ITNative)) False PTAny $ binop "+"
  , item (LPlus (ATInt (ITFixed IT8))) False PTAny $ JsForeign "%0 + %1 & 0xFF"
  , item (LPlus (ATInt (ITFixed IT16))) False PTAny $ JsForeign "%0 + %1 & 0xFFFF"
  , item (LPlus (ATInt (ITFixed IT32))) False PTAny $ JsForeign "%0+%1|0"
  , item (LPlus (ATInt ITBig)) True PTAny $ method "add"
  , item (LPlus (ATInt (ITFixed IT64))) True PTAny $
    \[l, r] -> JsForeign "%0.add(%1).and(new $JSRTS.jsbn.BigInteger(%2))" [l,r, JsStr $ show 0xFFFFFFFFFFFFFFFF]
  , item (LMinus ATFloat) False PTAny $ binop "-"
  , item (LMinus (ATInt ITChar)) False PTAny $ JsForeign "String.fromCharCode(%0.charCodeAt(0) - %1.charCodeAt(0))"
  , item (LMinus (ATInt ITNative)) False PTAny $ binop "-"
  , item (LMinus (ATInt (ITFixed IT8))) False PTAny $ JsForeign "%0 - %1 & 0xFF"
  , item (LMinus (ATInt (ITFixed IT16))) False PTAny $ JsForeign "%0 - %1 & 0xFFFF"
  , item (LMinus (ATInt (ITFixed IT32))) False PTAny $ JsForeign "%0-%1|0"
  , item (LMinus (ATInt ITBig)) True PTAny $ method "subtract"
  , item (LMinus (ATInt (ITFixed IT64))) True PTAny $
    \[l, r] -> JsForeign "%0.subtract(%1).and(new $JSRTS.jsbn.BigInteger(%2))" [l,r, JsStr $ show 0xFFFFFFFFFFFFFFFF]
  , item (LTimes ATFloat) False PTAny $ binop "*"
  , item (LTimes (ATInt ITChar)) False PTAny $ JsForeign "String.fromCharCode(%0.charCodeAt(0) * %1.charCodeAt(0))"
  , item (LTimes (ATInt ITNative)) False PTAny $ binop "*"
  , item (LTimes (ATInt (ITFixed IT8))) False PTAny $ JsForeign "%0 * %1 & 0xFF"
  , item (LTimes (ATInt (ITFixed IT16))) False PTAny $ JsForeign "%0 * %1 & 0xFFFF"
  , item (LTimes (ATInt (ITFixed IT32))) False PTAny $ JsForeign "%0*%1|0"
  , item (LTimes (ATInt ITBig)) True PTAny $ method "multiply"
  , item (LTimes (ATInt (ITFixed IT64))) True PTAny $
    \[l, r] -> JsForeign "%0.multiply(%1).and(new $JSRTS.jsbn.BigInteger(%2))" [l,r, JsStr $ show 0xFFFFFFFFFFFFFFFF]
  , item (LUDiv (ITFixed IT8)) False PTAny $ JsForeign "%0 / %1"
  , item (LUDiv (ITFixed IT16)) False PTAny $ JsForeign "%0 / %1"
  , item (LUDiv (ITFixed IT32)) False PTAny $ JsForeign "(%0>>>0)  / (%1>>>0) |0"
  , item (LUDiv (ITFixed IT64)) True PTAny $ JsForeign "%0.divide(%1)"
  , item (LSDiv ATFloat) False PTAny $ binop "/"
  , item (LSDiv (ATInt (ITFixed IT8))) False PTAny $ JsForeign "%0 / %1"
  , item (LSDiv (ATInt (ITFixed IT16))) False PTAny $ JsForeign "%0 / %1"
  , item (LSDiv (ATInt (ITFixed IT32))) False PTAny $ JsForeign "%0  / %1 |0"
  , item (LSDiv (ATInt (ITFixed IT64))) True PTAny $ JsForeign "%0.divide(%1)"
  , item (LSDiv (ATInt ITNative)) False PTAny $ JsForeign "%0/%1|0" -- we need "|0" in this
  , item (LSDiv (ATInt ITBig)) True PTAny $ method "divide"
  , item (LURem (ITFixed IT8)) False PTAny $ JsForeign "%0 % %1"
  , item (LURem (ITFixed IT16)) False PTAny $ JsForeign "%0 % %1"
  , item (LURem (ITFixed IT32)) False PTAny $ JsForeign "(%0>>>0) % (%1>>>0) |0"
  , item (LURem (ITFixed IT64)) True PTAny $ method "remainder"
  , item (LSRem ATFloat) False PTAny $ binop "%"
  , item (LSRem (ATInt ITNative)) False PTAny $ binop "%"
  , item (LSRem (ATInt (ITFixed IT8))) False PTAny $ JsForeign "%0 % %1"
  , item (LSRem (ATInt (ITFixed IT16))) False PTAny $ JsForeign "%0 % %1"
  , item (LSRem (ATInt (ITFixed IT32))) False PTAny $ JsForeign "%0 % %1 |0"
  , item (LSRem (ATInt (ITFixed IT64))) True PTAny $ method "remainder"
  , item (LSRem (ATInt ITBig)) True PTAny $ method "remainder"
  , item (LAnd ITNative) False PTAny $ JsForeign "%0 & %1"
  , item (LAnd (ITFixed IT8)) False PTAny $ JsForeign "%0 & %1"
  , item (LAnd (ITFixed IT16)) False PTAny $ JsForeign "%0 & %1"
  , item (LAnd (ITFixed IT32)) False PTAny $ JsForeign "%0  & %1"
  , item (LAnd (ITFixed IT64)) True PTAny $ method "and"
  , item (LAnd ITBig) True PTAny $ method "and"
  , item (LOr ITNative) False PTAny $ JsForeign "%0 | %1"
  , item (LOr (ITFixed IT8)) False PTAny $ JsForeign "%0 | %1"
  , item (LOr (ITFixed IT16)) False PTAny $ JsForeign "%0 | %1"
  , item (LOr (ITFixed IT32)) False PTAny $ JsForeign "%0 | %1"
  , item (LOr (ITFixed IT64)) True PTAny $ method "or"
  , item (LOr ITBig) True PTAny $ method "or"
  , item (LXOr ITNative) False PTAny $ JsForeign "%0 ^ %1"
  , item (LXOr (ITFixed IT8)) False PTAny $ JsForeign "%0 ^ %1"
  , item (LXOr (ITFixed IT16)) False PTAny $ JsForeign "%0 ^ %1"
  , item (LXOr (ITFixed IT32)) False PTAny $ JsForeign "%0 ^ %1"
  , item (LXOr (ITFixed IT64)) True PTAny $ method "xor"
  , item (LXOr ITBig) True PTAny $ method "xor"
  , item (LSHL ITNative) False PTAny $ JsForeign "%0 << %1 |0"
  , item (LSHL (ITFixed IT8)) False PTAny $ JsForeign "%0 << %1 & 0xFF"
  , item (LSHL (ITFixed IT16)) False PTAny $ JsForeign "%0 << %1 & 0xFFFF"
  , item (LSHL (ITFixed IT32)) False PTAny $ JsForeign "%0 << %1 | 0"
  , item (LSHL (ITFixed IT64)) True PTAny $
    \[l, r] -> JsForeign "%0.shiftLeft(%1).and(new $JSRTS.jsbn.BigInteger(%2))" [l,r, JsStr $ show 0xFFFFFFFFFFFFFFFF]
  , item (LSHL ITBig) True PTAny $ method "shiftLeft"
  , item (LLSHR ITNative) False PTAny $ JsForeign "%0 >>> %1 |0"
  , item (LLSHR (ITFixed IT8)) False PTAny $ JsForeign "%0 >>> %1"
  , item (LLSHR (ITFixed IT16)) False PTAny $ JsForeign "%0 >>> %1"
  , item (LLSHR (ITFixed IT32)) False PTAny $ JsForeign "%0 >>> %1|0"
  , item (LLSHR (ITFixed IT64)) True PTAny $ JsForeign "%0.shiftRight(%1)"
  , item (LASHR ITNative) False PTAny $ JsForeign "%0 >> %1 |0"
  , item (LASHR (ITFixed IT8)) False PTAny $ JsForeign "%0 >> %1"
  , item (LASHR (ITFixed IT16)) False PTAny $ JsForeign "%0 >> %1"
  , item (LASHR (ITFixed IT32)) False PTAny $ JsForeign "%0 >> %1|0"
  , item (LASHR (ITFixed IT64)) True PTAny $ JsForeign "%0.shiftRight(%1)"
  , item (LCompl (ITFixed IT8)) False PTAny $ JsForeign "~%0"
  , item (LCompl (ITFixed IT16)) False PTAny $ JsForeign "~%0"
  , item (LCompl (ITFixed IT32)) False PTAny $ JsForeign "~%0|0"
  , item (LCompl (ITFixed IT64)) True PTAny $ method "not"
  , item (LEq ATFloat) False PTBool $ binop "==="
  , item (LEq (ATInt ITNative)) False PTBool $ binop "==="
  , item (LEq (ATInt ITChar)) False PTBool $ binop "==="
  , item (LEq (ATInt ITBig)) True PTBool $ method "equals"
  , item (LEq (ATInt (ITFixed IT8))) False PTBool $ binop "==="
  , item (LEq (ATInt (ITFixed IT16))) False PTBool $ binop "==="
  , item (LEq (ATInt (ITFixed IT32))) False PTBool $ binop "==="
  , item (LEq (ATInt (ITFixed IT64))) True PTBool $ method "equals"
  , item (LLt (ITFixed IT8)) False PTBool $ JsForeign "%0 < %1"
  , item (LLt (ITFixed IT16)) False PTBool $ JsForeign "%0 < %1"
  , item (LLt (ITFixed IT32)) False PTBool $ JsForeign "(%0>>>0) < (%1>>>0)"
  , item (LLt (ITFixed IT64)) True PTBool $ JsForeign "%0.compareTo(%1) < 0"
  , item (LLe (ITFixed IT8)) False PTBool $ JsForeign "%0 <= %1"
  , item (LLe (ITFixed IT16)) False PTBool $ JsForeign "%0 <= %1"
  , item (LLe (ITFixed IT32)) False PTBool $ JsForeign "(%0>>>0) <= (%1>>>0)"
  , item (LLe (ITFixed IT64)) True PTBool $ JsForeign "%0.compareTo(%1) <= 0"
  , item (LGt (ITFixed IT8)) False PTBool $ JsForeign "%0 > %1"
  , item (LGt (ITFixed IT16)) False PTBool $ JsForeign "%0 > %1"
  , item (LGt (ITFixed IT32)) False PTBool $ JsForeign "(%0>>>0) > (%1>>>0)"
  , item (LGt (ITFixed IT64)) True PTBool $ JsForeign "%0.compareTo(%1) > 0"
  , item (LGe (ITFixed IT8)) False PTBool $ JsForeign "%0 >= %1"
  , item (LGe (ITFixed IT16)) False PTBool $ JsForeign "%0 >= %1"
  , item (LGe (ITFixed IT32)) False PTBool $ JsForeign "(%0>>>0) >= (%1>>>0)"
  , item (LGe (ITFixed IT64)) True PTBool $ JsForeign "%0.compareTo(%1) >= 0"
  , item (LSLt ATFloat) False PTBool $ binop "<"
  , item (LSLt (ATInt ITChar)) False PTBool $ binop "<"
  , item (LSLt (ATInt ITNative)) False PTBool $ binop "<"
  , item (LSLt (ATInt ITBig)) True PTBool $ JsForeign "%0.compareTo(%1) < 0"
  , item (LSLt (ATInt (ITFixed IT8))) False PTBool $ binop "<"
  , item (LSLt (ATInt (ITFixed IT16))) False PTBool $ binop "<"
  , item (LSLt (ATInt (ITFixed IT32))) False PTBool $ binop "<"
  , item (LSLt (ATInt (ITFixed IT64))) True PTBool $ JsForeign "%0.compareTo(%1) < 0"
  , item (LSLe ATFloat) False PTBool $ binop "<="
  , item (LSLe (ATInt ITNative)) False PTBool $ binop "<="
  , item (LSLe (ATInt ITBig)) True PTBool $ JsForeign "%0.compareTo(%1) <= 0"
  , item (LSLe (ATInt (ITFixed IT8))) False PTBool $ binop "<="
  , item (LSLe (ATInt (ITFixed IT16))) False PTBool $ binop "<="
  , item (LSLe (ATInt (ITFixed IT32))) False PTBool $ binop "<="
  , item (LSLe (ATInt (ITFixed IT64))) True PTBool $ JsForeign "%0.compareTo(%1) <= 0"
  , item (LSGt ATFloat) False PTBool $ binop ">"
  , item (LSGt (ATInt ITNative)) False PTBool $ binop ">"
  , item (LSGt (ATInt ITBig)) True PTBool $ JsForeign "%0.compareTo(%1) > 0"
  , item (LSGt (ATInt (ITFixed IT8))) False PTBool $ binop ">"
  , item (LSGt (ATInt (ITFixed IT16))) False PTBool $ binop ">"
  , item (LSGt (ATInt (ITFixed IT32))) False PTBool $ binop ">"
  , item (LSGt (ATInt (ITFixed IT64))) True PTBool $ JsForeign "%0.compareTo(%1) > 0"
  , item (LSGe ATFloat) False PTBool $ binop ">="
  , item (LSGe (ATInt ITNative)) False PTBool $ binop ">="
  , item (LSGe (ATInt ITBig)) True PTBool $ JsForeign "%0.compareTo(%1) >= 0"
  , item (LSGe (ATInt (ITFixed IT8))) False PTBool $ binop ">="
  , item (LSGe (ATInt (ITFixed IT16))) False PTBool $ binop ">="
  , item (LSGe (ATInt (ITFixed IT32))) False PTBool $ binop ">="
  , item (LSGe (ATInt (ITFixed IT64))) True PTBool $ JsForeign "%0.compareTo(%1) >= 0"
  , item (LSExt ITNative ITBig) True PTAny $ JsForeign "new $JSRTS.jsbn.BigInteger(''+%0)"
  , item (LZExt (ITFixed IT8) ITNative) False PTAny $ head
  , item (LZExt (ITFixed IT16) ITNative) False PTAny $ head
  , item (LZExt (ITFixed IT32) ITNative) False PTAny $ head
  , item (LZExt ITNative ITBig) True PTAny $ JsForeign "new $JSRTS.jsbn.BigInteger(''+%0)"
  , item (LZExt (ITFixed IT8) ITBig) True PTAny $ JsForeign "new $JSRTS.jsbn.BigInteger(''+%0)"
  , item (LZExt (ITFixed IT16) ITBig) True PTAny $ JsForeign "new $JSRTS.jsbn.BigInteger(''+%0)"
  , item (LZExt (ITFixed IT32) ITBig) True PTAny $ JsForeign "new $JSRTS.jsbn.BigInteger(''+%0)"
  , item (LZExt (ITFixed IT64) ITBig) True PTAny $ head
  , item (LTrunc ITBig ITNative) True PTAny $ JsForeign "%0.intValue()|0"
  , item (LTrunc ITBig (ITFixed IT8)) True PTAny $ JsForeign "%0.intValue() & 0xFF"
  , item (LTrunc ITBig (ITFixed IT16)) True PTAny $ JsForeign "%0.intValue() & 0xFFFF"
  , item (LTrunc ITBig (ITFixed IT32)) True PTAny $ JsForeign "%0.intValue() & 0xFFFFFFFF"
  , item (LTrunc ITBig (ITFixed IT64)) True PTAny $
    \[x] -> JsForeign "%0.and(new $JSRTS.jsbn.BigInteger(%1))" [x, JsStr $ show 0xFFFFFFFFFFFFFFFF]
  , item (LTrunc (ITFixed IT16) (ITFixed IT8)) False PTAny $ JsForeign "%0 & 0xFF"
  , item (LTrunc (ITFixed IT32) (ITFixed IT8)) False PTAny $ JsForeign "%0 & 0xFF"
  , item (LTrunc (ITFixed IT64) (ITFixed IT8)) True PTAny $ JsForeign "%0.intValue() & 0xFF"
  , item (LTrunc (ITFixed IT32) (ITFixed IT16)) False PTAny $ JsForeign "%0 & 0xFFFF"
  , item (LTrunc (ITFixed IT64) (ITFixed IT16)) True PTAny $ JsForeign "%0.intValue() & 0xFFFF"
  , item (LTrunc (ITFixed IT64) (ITFixed IT32)) True PTAny $ JsForeign "%0.intValue() & 0xFFFFFFFF"
  , item LStrConcat False PTAny $ binop "+"
  , item LStrLt False PTBool $ binop "<"
  , item LStrEq False PTBool $ binop "=="
  , item LStrLen False PTAny $ JsForeign "%0.length"
  , item (LIntFloat ITNative) False PTAny $ head
  , item (LIntFloat ITBig) True PTAny $ JsForeign "%0.intValue()"
  , item (LFloatInt ITNative) False PTAny $ JsForeign "%0|0"
  , item (LFloatInt ITBig) True PTAny $ JsForeign "new $JSRTS.jsbn.BigInteger(Math.trunc(%0)+ '')"
  , item (LIntStr ITNative) False PTAny $ JsForeign "''+%0"
  , item (LIntStr ITBig) True PTAny $ JsForeign "%0.toString()"
  , item (LStrInt ITNative) False PTAny $ JsForeign "parseInt(%0)|0"
  , item (LStrInt ITBig) True PTAny $ JsForeign "new $JSRTS.jsbn.BigInteger(%0)"
  , item (LFloatStr) False PTAny $ JsForeign "''+%0"
  , item (LStrFloat) False PTAny $ jsAppN "parseFloat"
  , item (LChInt ITNative) False PTAny $ JsForeign "%0.charCodeAt(0)|0"
  , item (LIntCh ITNative) False PTAny $ jsAppN "String.fromCharCode"
  , item LFExp False PTAny $ jsAppN "Math.exp"
  , item LFLog False PTAny $ jsAppN "Math.log"
  , item LFSin False PTAny $ jsAppN "Math.sin"
  , item LFCos False PTAny $ jsAppN "Math.cos"
  , item LFTan False PTAny $ jsAppN "Math.tan"
  , item LFASin False PTAny $ jsAppN "Math.asin"
  , item LFACos False PTAny $ jsAppN "Math.acos"
  , item LFATan False PTAny $ jsAppN "Math.atan"
  , item LFATan2 False PTAny $ jsAppN "Math.atan2"
  , item LFSqrt False PTAny $ jsAppN "Math.sqrt"
  , item LFFloor False PTAny $ jsAppN "Math.floor"
  , item LFCeil False PTAny $ jsAppN "Math.ceil"
  , item LFNegate False PTAny $ JsForeign "-%0"
  , item LStrHead False PTAny $ \[x] -> JsArrayProj (JsInt 0) x
  , item LStrTail False PTAny $ \[x] -> JsMethod x "slice" [JsInt 1]
  , item LStrCons False PTAny $ JsForeign "%0+%1"
  , item LStrIndex False PTAny $ \[x, y] -> JsArrayProj y x
  , item LStrRev False PTAny $ JsForeign "%0.split('').reverse().join('')"
  , item LStrSubstr False PTAny $ JsForeign "$JSRTS.prim_strSubstr(%0, %1, %2)"
  , item LSystemInfo False PTAny $ JsApp (JsProp (JsVar "$JSRTS") "prim_systemInfo")
  , item LCrash False PTAny $ \[l] -> JsErrorExp l
  , item LReadStr False PTAny $ \[_] -> JsApp (JsProp (JsVar "$JSRTS") "prim_readStr") []
  , item LWriteStr False PTAny $ \[_, str] -> JsApp (JsProp (JsVar "$JSRTS") "prim_writeStr") [str]
  , item LNoOp False PTAny $ head
  ]
  where
    item :: PrimFn -> Bool -> JsPrimTy -> PrimF -> (PrimFn, PrimDec)
    item fn ubi pty c = (fn, (ubi, pty, c))
    binop op [l, r] = JsBinOp op l r
    method op (l:r) = JsMethod l op r

jsB2I :: JsExpr -> JsExpr
jsB2I x = JsForeign "%0 ? 1|0 : 0|0" [x]

jsPrimCoerce :: JsPrimTy -> JsPrimTy -> JsExpr -> JsExpr
jsPrimCoerce PTBool PTAny x = jsB2I x
jsPrimCoerce _ _ x = x

{-# LANGUAGE PatternGuards #-}
module IRTS.Java.JTypes where

import           Idris.Core.TT
import           IRTS.Lang
import           Language.Java.Syntax
import qualified Language.Java.Syntax as J

import qualified Data.Vector.Unboxed  as V

-----------------------------------------------------------------------
-- Primitive types

charType :: J.Type
charType =
  PrimType CharT

byteType :: J.Type
byteType = PrimType ByteT

shortType :: J.Type
shortType = PrimType ShortT

integerType :: J.Type
integerType = PrimType IntT

longType :: J.Type
longType = PrimType LongT

doubleType :: J.Type
doubleType = PrimType DoubleT

array :: J.Type -> J.Type
array t = RefType . ArrayType $ t

addressType :: J.Type
addressType = longType

-----------------------------------------------------------------------
-- Boxed types

objectType :: J.Type
objectType =
  RefType . ClassRefType $ ClassType [(Ident "Object", [])]

bigIntegerType :: J.Type
bigIntegerType =
  RefType . ClassRefType $ ClassType [(Ident "BigInteger", [])]

stringType :: J.Type
stringType =
  RefType . ClassRefType $ ClassType [(Ident "String", [])]

bufferType :: J.Type
bufferType =
  RefType . ClassRefType $ ClassType [(Ident "ByteBuffer", [])]

threadType :: J.Type
threadType =
  RefType . ClassRefType $ ClassType [(Ident "Thread", [])]

callableType :: J.Type
callableType =
  RefType . ClassRefType $ ClassType [(Ident "Callable", [])]

voidType :: J.Type
voidType =
  RefType . ClassRefType $ ClassType [(Ident "Void", [])]

box :: J.Type -> J.Type
box (PrimType CharT  ) = RefType . ClassRefType $ ClassType [(Ident "Character", [])]
box (PrimType ByteT  ) = RefType . ClassRefType $ ClassType [(Ident "Byte", [])]
box (PrimType ShortT ) = RefType . ClassRefType $ ClassType [(Ident "Short", [])]
box (PrimType IntT   ) = RefType . ClassRefType $ ClassType [(Ident "Integer", [])]
box (PrimType LongT  ) = RefType . ClassRefType $ ClassType [(Ident "Long", [])]
box (PrimType DoubleT) = RefType . ClassRefType $ ClassType [(Ident "Double", [])]
box t = t

isFloating :: J.Type -> Bool
isFloating (PrimType DoubleT) = True
isFloating (PrimType FloatT)  = True
isFloating _ = False

isPrimitive :: J.Type -> Bool
isPrimitive (PrimType _) = True
isPrimitive _ = False

isArray :: J.Type -> Bool
isArray (RefType (ArrayType  _)) = True
isArray _ = False

isString :: J.Type -> Bool
isString (RefType (ClassRefType (ClassType [(Ident "String", _)]))) = True
isString _ = False

-----------------------------------------------------------------------
-- Idris rts classes

idrisClosureType :: J.Type
idrisClosureType =
  RefType . ClassRefType $ ClassType [(Ident "Closure", [])]

idrisTailCallClosureType :: J.Type
idrisTailCallClosureType =
  RefType . ClassRefType $ ClassType [(Ident "TailCallClosure", [])]

idrisObjectType :: J.Type
idrisObjectType =
  RefType . ClassRefType $ ClassType [(Ident "IdrisObject", [])]

foreignWrapperType :: J.Type
foreignWrapperType =
  RefType . ClassRefType $ ClassType [(Ident "ForeignWrapper", [])]

primFnType :: J.Type
primFnType =
  RefType . ClassRefType $ ClassType [(Ident "PrimFn", [])]

-----------------------------------------------------------------------
-- Java utility classes

arraysType :: J.Type
arraysType =
  RefType . ClassRefType $ ClassType [(Ident "Arrays", [])]

mathType :: J.Type
mathType =
  RefType . ClassRefType $ ClassType [(Ident "Math", [])]


-----------------------------------------------------------------------
-- Exception types

exceptionType :: J.Type
exceptionType =
  RefType . ClassRefType $ ClassType [(Ident "Exception", [])]

runtimeExceptionType :: J.Type
runtimeExceptionType =
  RefType . ClassRefType $ ClassType [(Ident "RuntimeException", [])]

-----------------------------------------------------------------------
-- Integer types

nativeTyToJType :: NativeTy -> J.Type
nativeTyToJType IT8  = byteType
nativeTyToJType IT16 = shortType
nativeTyToJType IT32 = integerType
nativeTyToJType IT64 = longType

intTyToJType :: IntTy -> J.Type
intTyToJType (ITFixed nt) = nativeTyToJType nt
intTyToJType (ITNative)   = integerType
intTyToJType (ITBig)      = bigIntegerType
intTyToJType (ITChar)     = charType
intTyToJType (ITVec nt _) = array $ nativeTyToJType nt

arithTyToJType :: ArithTy -> J.Type
arithTyToJType (ATInt it) = intTyToJType it
arithTyToJType (ATFloat) = doubleType

-----------------------------------------------------------------------
-- Context variables

localContextID :: Ident
localContextID = Ident "context"

localContext :: Exp
localContext = ExpName $ Name [localContextID]

globalContextID :: Ident
globalContextID = Ident "globalContext"

globalContext :: Exp
globalContext = ExpName $ Name [globalContextID]

newContextID :: Ident
newContextID = Ident "new_context"

newContext :: Exp
newContext = ExpName $ Name [newContextID]

contextArray :: LVar -> Exp
contextArray (Loc _) = localContext
contextArray (Glob _) = globalContext

contextParam :: FormalParam
contextParam = FormalParam [Final] (array objectType) False (VarId localContextID)

-----------------------------------------------------------------------
-- Constant types

constType :: Const -> J.Type
constType (I    _) = arithTyToJType (ATInt ITNative)
constType (BI   _) = arithTyToJType (ATInt ITBig   )
constType (Fl   _) = arithTyToJType (ATFloat       )
constType (Ch   _) = arithTyToJType (ATInt ITChar  )
constType (Str  _) = stringType
constType (B8   _) = arithTyToJType (ATInt $ ITFixed IT8 )
constType (B16  _) = arithTyToJType (ATInt $ ITFixed IT16)
constType (B32  _) = arithTyToJType (ATInt $ ITFixed IT32)
constType (B64  _) = arithTyToJType (ATInt $ ITFixed IT64)
constType (B8V  v) = arithTyToJType (ATInt . ITVec IT8 $ V.length v)
constType (B16V v) = arithTyToJType (ATInt . ITVec IT16 $ V.length v)
constType (B32V v) = arithTyToJType (ATInt . ITVec IT32 $ V.length v)
constType (B64V v) = arithTyToJType (ATInt . ITVec IT64 $ V.length v)
constType _        = objectType

-----------------------------------------------------------------------
-- Foreign types

foreignType :: FType -> Maybe J.Type
foreignType (FArith      at) = Just $ arithTyToJType at
foreignType (FFunction     ) = Just $ callableType
foreignType (FFunctionIO   ) = Just $ callableType
foreignType (FString       ) = Just $ stringType
foreignType (FUnit         ) = Nothing
foreignType (FPtr          ) = Just $ objectType
foreignType (FAny          ) = Just $ objectType

-----------------------------------------------------------------------
-- Primitive operation analysis

opName :: PrimFn -> String
opName x
  | (LSExt _ to)   <- x = "LSExt" ++ (suffixFor to)
  | (LZExt _ to)   <- x = "LZExt" ++ (suffixFor to)
  | (LTrunc _ to)  <- x = "LTrunc" ++ (suffixFor to)
  | (LFloatInt to) <- x = "LFloatInt" ++ (suffixFor to)
  | (LStrInt to)   <- x = "LStrInt" ++ (suffixFor to)
  | (LChInt to)    <- x = "LChInt" ++ (suffixFor to)
  | (LPeek to _)   <- x = "LPeek" ++ (suffixFor to)
  | otherwise = takeWhile ((/=) ' ') $ show x
  where
    suffixFor (ITFixed nt) = show nt
    suffixFor (ITNative) = show IT32
    suffixFor (ITBig) = show ITBig
    suffixFor (ITChar) = show ITChar
    suffixFor (ITVec nt _) = "ITVec" ++ (show $ nativeTyWidth nt)

sourceTypes :: PrimFn -> [J.Type]
sourceTypes (LPlus from) = [arithTyToJType from, arithTyToJType from]
sourceTypes (LMinus from) = [arithTyToJType from, arithTyToJType from]
sourceTypes (LTimes from) = [arithTyToJType from, arithTyToJType from]
sourceTypes (LUDiv from) = [intTyToJType from, intTyToJType from]
sourceTypes (LSDiv from) = [arithTyToJType from, arithTyToJType from]
sourceTypes (LURem from) = [intTyToJType from, intTyToJType from]
sourceTypes (LSRem from) = [arithTyToJType from, arithTyToJType from]
sourceTypes (LAnd from) = [intTyToJType from, intTyToJType from]
sourceTypes (LOr from) = [intTyToJType from, intTyToJType from]
sourceTypes (LXOr from) = [intTyToJType from, intTyToJType from]
sourceTypes (LCompl from) = [intTyToJType from]
sourceTypes (LSHL from) = [intTyToJType from, intTyToJType from]
sourceTypes (LLSHR from) = [intTyToJType from, intTyToJType from]
sourceTypes (LASHR from) = [intTyToJType from, intTyToJType from]
sourceTypes (LEq from) = [arithTyToJType from, arithTyToJType from]
sourceTypes (LSLt from) = [arithTyToJType from, arithTyToJType from]
sourceTypes (LSLe from) = [arithTyToJType from, arithTyToJType from]
sourceTypes (LSGt from) = [arithTyToJType from, arithTyToJType from]
sourceTypes (LSGe from) = [arithTyToJType from, arithTyToJType from]
sourceTypes (LLt from) = [intTyToJType from, intTyToJType from]
sourceTypes (LLe from) = [intTyToJType from, intTyToJType from]
sourceTypes (LGt from) = [intTyToJType from, intTyToJType from]
sourceTypes (LGe from) = [intTyToJType from, intTyToJType from]
sourceTypes (LSExt from _) = [intTyToJType from]
sourceTypes (LZExt from _) = [intTyToJType from]
sourceTypes (LTrunc from _) = [intTyToJType from]
sourceTypes (LStrConcat) = repeat stringType
sourceTypes (LStrLt) = [stringType, stringType]
sourceTypes (LStrEq) = [stringType, stringType]
sourceTypes (LStrLen) = [stringType]
sourceTypes (LIntFloat from) = [intTyToJType from]
sourceTypes (LFloatInt _) = [doubleType]
sourceTypes (LIntStr from) = [intTyToJType from]
sourceTypes (LStrInt from) = [stringType]
sourceTypes (LFloatStr) = [doubleType]
sourceTypes (LStrFloat) = [stringType]
sourceTypes (LChInt _) = [charType]
sourceTypes (LIntCh from) = [intTyToJType from]
sourceTypes (LPrintNum) = [objectType]
sourceTypes (LPrintStr) = [stringType]
sourceTypes (LReadStr) = [objectType]
sourceTypes (LFExp) = [doubleType]
sourceTypes (LFLog) = [doubleType]
sourceTypes (LFSin) = [doubleType]
sourceTypes (LFCos) = [doubleType]
sourceTypes (LFTan) = [doubleType]
sourceTypes (LFASin) = [doubleType]
sourceTypes (LFACos) = [doubleType]
sourceTypes (LFATan) = [doubleType]
sourceTypes (LFSqrt) = [doubleType]
sourceTypes (LFFloor) = [doubleType]
sourceTypes (LFCeil) = [doubleType]
sourceTypes (LMkVec nt n) = replicate n (nativeTyToJType nt)
sourceTypes (LIdxVec nt _) = [array $ nativeTyToJType nt, integerType]
sourceTypes (LUpdateVec nt _) = [array $ nativeTyToJType nt, integerType, nativeTyToJType nt]
sourceTypes (LStrHead) = [stringType]
sourceTypes (LStrTail) = [stringType]
sourceTypes (LStrCons) = [charType, stringType]
sourceTypes (LStrIndex) = [stringType, integerType]
sourceTypes (LStrRev) = [stringType]
sourceTypes (LStdIn) = []
sourceTypes (LStdOut) = []
sourceTypes (LStdErr) = []
sourceTypes (LAllocate) = [addressType]
sourceTypes (LAppendBuffer) =
  [bufferType, addressType, addressType, addressType, addressType, bufferType]
sourceTypes (LSystemInfo) = [integerType]
sourceTypes (LAppend nt _) = [bufferType, addressType, addressType, intTyToJType nt]
sourceTypes (LPeek _ _) = [bufferType, addressType]
sourceTypes (LFork) = [objectType]
sourceTypes (LPar) = [objectType]
sourceTypes (LVMPtr) = []
sourceTypes (LNullPtr) = [objectType]
sourceTypes (LNoOp) = repeat objectType

-----------------------------------------------------------------------
-- Endianess markers

endiannessConstant :: Endianness -> Exp
endiannessConstant c =
  ExpName . Name . map Ident $ ["java", "nio", "ByteOrder", endiannessConstant' c]
  where
    endiannessConstant' BE                 = "BIG_ENDIAN"
    endiannessConstant' LE                 = "LITTLE_ENDIAN"
    endiannessConstant' (IRTS.Lang.Native) = endiannessConstant' BE

endiannessArguments :: PrimFn -> [Exp]
endiannessArguments (LAppend _ end) = [endiannessConstant end]
endiannessArguments (LPeek _ end)   = [endiannessConstant end]
endiannessArguments _               = []

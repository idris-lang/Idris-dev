{-|
Module      : IRTS.Portable
Description : Serialise Idris' IR to JSON.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE OverloadedStrings #-}
module IRTS.Portable (writePortable) where

import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT
import IRTS.Bytecode
import IRTS.CodegenCommon
import IRTS.Defunctionalise
import IRTS.Lang
import IRTS.Simplified

import Data.Aeson
import qualified Data.ByteString.Lazy as B
import qualified Data.Text as T
import System.IO

data CodegenFile = CGFile {
    fileType :: String,
    version :: Int,
    cgInfo :: CodegenInfo
}

-- Update the version when the format changes
formatVersion :: Int
formatVersion = 3

writePortable :: Handle -> CodegenInfo -> IO ()
writePortable file ci = do
    let json = encode $ CGFile "idris-codegen" formatVersion ci
    B.hPut file json

instance ToJSON CodegenFile where
    toJSON (CGFile ft v ci) = object ["file-type" .= ft,
                                      "version" .= v,
                                      "codegen-info" .= toJSON ci]

instance ToJSON CodegenInfo where
    toJSON ci = object ["output-file" .= (outputFile ci),
                        "includes" .= (includes ci),
                        "import-dirs" .= (importDirs ci),
                        "compile-objs" .= (compileObjs ci),
                        "compile-libs" .= (compileLibs ci),
                        "compiler-flags" .= (compilerFlags ci),
                        "interfaces" .= (interfaces ci),
                        "exports" .= (exportDecls ci),
                        "lift-decls" .= (liftDecls ci),
                        "defun-decls" .= (defunDecls ci),
                        "simple-decls" .= (simpleDecls ci),
                        "bytecode" .= (map toBC (simpleDecls ci)),
                        "tt-decls" .= (ttDecls ci)]

instance ToJSON Name where
    toJSON n = toJSON $ showCG n

instance ToJSON ExportIFace where
    toJSON (Export n f xs) = object ["ffi-desc" .= n,
                                     "interface-file" .= f,
                                     "exports" .= xs]

instance ToJSON FDesc where
    toJSON (FCon n) = object ["FCon" .= n]
    toJSON (FStr s) = object ["FStr" .= s]
    toJSON (FUnknown) = object ["FUnknown" .= Null]
    toJSON (FIO fd) = object ["FIO" .= fd]
    toJSON (FApp n xs) = object ["FApp" .= (n, xs)]

instance ToJSON Export where
    toJSON (ExportData fd) = object ["ExportData" .= fd]
    toJSON (ExportFun n dsc ret args) = object ["ExportFun" .= (n, dsc, ret, args)]

instance ToJSON LDecl where
    toJSON (LFun opts name args def) = object ["LFun" .= (opts, name, args, def)]
    toJSON (LConstructor name tag ar) = object ["LConstructor" .= (name, tag, ar)]

instance ToJSON LOpt where
    toJSON Inline = String "Inline"
    toJSON NoInline = String "NoInline"

instance ToJSON LExp where
    toJSON (LV lv) = object ["LV" .= lv]
    toJSON (LApp tail exp args) = object ["LApp" .= (tail, exp, args)]
    toJSON (LLazyApp name exps) = object ["LLazyApp" .= (name, exps)]
    toJSON (LLazyExp exp) = object ["LLazyExp" .= exp]
    toJSON (LForce exp) = object ["LForce" .= exp]
    toJSON (LLet name a b) = object ["LLet" .= (name, a, b)]
    toJSON (LLam args exp) = object ["LLam" .= (args, exp)]
    toJSON (LProj exp i) = object ["LProj" .= (exp, i)]
    toJSON (LCon lv i n exps) = object ["LCon" .= (lv, i, n, exps)]
    toJSON (LCase ct exp alts) = object ["LCase" .= (ct, exp, alts)]
    toJSON (LConst c) = object ["LConst" .= c]
    toJSON (LForeign fd ret exps) = object ["LForeign" .= (fd, ret, exps)]
    toJSON (LOp prim exps) = object ["LOp" .= (prim, exps)]
    toJSON LNothing = object ["LNothing" .= Null]
    toJSON (LError s) = object ["LError" .= s]

instance ToJSON LVar where
    toJSON (Loc i) = object ["Loc" .= i]
    toJSON (Glob n) = object ["Glob" .= n]

instance ToJSON CaseType where
    toJSON Updatable = String "Updatable"
    toJSON Shared = String "Shared"

instance ToJSON LAlt where
    toJSON (LConCase i n ns exp) = object ["LConCase" .= (i, n, ns, exp)]
    toJSON (LConstCase c exp) = object ["LConstCase" .= (c, exp)]
    toJSON (LDefaultCase exp) = object ["LDefaultCase" .= exp]

instance ToJSON Const where
    toJSON (I i) = object ["int" .= i]
    toJSON (BI i) = object ["bigint" .= (show i)]
    toJSON (Fl d) = object ["double" .= d]
    toJSON (Ch c) = object ["char" .= (show c)]
    toJSON (Str s) = object ["string" .= s]
    toJSON (B8 b) = object ["bits8" .= b]
    toJSON (B16 b) = object ["bits16" .= b]
    toJSON (B32 b) = object ["bits32" .= b]
    toJSON (B64 b) = object ["bits64" .= b]
    toJSON (AType at) = object ["atype" .= at]
    toJSON StrType = object ["strtype" .= Null]
    toJSON WorldType = object ["worldtype" .= Null]
    toJSON TheWorld = object ["theworld" .= Null]
    toJSON VoidType = object ["voidtype" .= Null]
    toJSON Forgot = object ["forgot" .= Null]

instance ToJSON ArithTy where
    toJSON (ATInt it) = object ["ATInt" .= it]
    toJSON ATFloat = object ["ATFloat" .= Null]

instance ToJSON IntTy where
    toJSON it = toJSON $ intTyName it

instance ToJSON PrimFn where
    toJSON (LPlus aty) = object ["LPlus" .= aty]
    toJSON (LMinus aty) = object ["LMinus" .= aty]
    toJSON (LTimes aty) = object ["LTimes" .= aty]
    toJSON (LUDiv aty) = object ["LUDiv" .= aty]
    toJSON (LSDiv aty) = object ["LSDiv" .= aty]
    toJSON (LAnd ity) = object ["LAnd" .= ity]
    toJSON (LOr ity) = object ["LOr" .= ity]
    toJSON (LXOr ity) = object ["LXOr" .= ity]
    toJSON (LCompl ity) = object ["LCompl" .= ity]
    toJSON (LSHL ity) = object ["LSHL" .= ity]
    toJSON (LLSHR ity) = object ["LLSHR" .= ity]
    toJSON (LASHR ity) = object ["LASHR" .= ity]
    toJSON (LEq aty) = object ["LEq" .= aty]
    toJSON (LLt ity) = object ["LLt" .= ity]
    toJSON (LLe ity) = object ["LLe" .= ity]
    toJSON (LGt ity) = object ["LGt" .= ity]
    toJSON (LGe ity) = object ["LGe" .= ity]
    toJSON (LSLt aty) = object ["LSLt" .= aty]
    toJSON (LSLe aty) = object ["LSLe" .= aty]
    toJSON (LSGt aty) = object ["LSGt" .= aty]
    toJSON (LSGe aty) = object ["LSGe" .= aty]
    toJSON (LZExt from to) = object ["LZExt" .= (from, to)]
    toJSON (LSExt from to) = object ["LSExt" .= (from, to)]
    toJSON (LTrunc from to) = object ["LTrunc" .= (from, to)]
    toJSON LStrConcat = object ["LStrConcat" .= Null]
    toJSON LStrLt = object ["LStrLt" .= Null]
    toJSON LStrEq = object ["LStrEq" .= Null]
    toJSON LStrLen = object ["LStrLen" .= Null]
    toJSON (LIntFloat ity) = object ["LIntFloat" .= ity]
    toJSON (LFloatInt ity) = object ["LFloatInt" .= ity]
    toJSON (LIntStr ity) = object ["LIntStr" .= ity]
    toJSON (LStrInt ity) = object ["LStrInt" .= ity]
    toJSON (LIntCh ity) = object ["LIntCh" .= ity]
    toJSON (LChInt ity) = object ["LChInt" .= ity]
    toJSON LFloatStr = object ["LFloatStr" .= Null]
    toJSON LStrFloat = object ["LStrFloat" .= Null]
    toJSON (LBitCast from to) = object ["LBitCast" .= (from, to)]
    toJSON LFExp = object ["LFExp" .= Null]
    toJSON LFLog = object ["LFLog" .= Null]
    toJSON LFSin = object ["LFSin" .= Null]
    toJSON LFCos = object ["LFCos" .= Null]
    toJSON LFTan = object ["LFTan" .= Null]
    toJSON LFASin = object ["LFASin" .= Null]
    toJSON LFACos = object ["LFACos" .= Null]
    toJSON LFATan = object ["LFATan" .= Null]
    toJSON LFSqrt = object ["LFSqrt" .= Null]
    toJSON LFFloor = object ["LFFloor" .= Null]
    toJSON LFCeil = object ["LFCeil" .= Null]
    toJSON LFNegate = object ["LFNegate" .= Null]
    toJSON LStrHead = object ["LStrHead" .= Null]
    toJSON LStrTail = object ["LStrTail" .= Null]
    toJSON LStrCons = object ["LStrCons" .= Null]
    toJSON LStrIndex = object ["LStrIndex" .= Null]
    toJSON LStrRev = object ["LStrRev" .= Null]
    toJSON LStrSubstr = object ["LStrSubstr" .= Null]
    toJSON LReadStr = object ["LReadStr" .= Null]
    toJSON LWriteStr = object ["LWriteStr" .= Null]
    toJSON LSystemInfo = object ["LSystemInfo" .= Null]
    toJSON LFork = object ["LFork" .= Null]
    toJSON LPar = object ["LPar" .= Null]
    toJSON (LExternal name) = object ["LExternal" .= name]
    toJSON LNoOp = object ["LNoOp" .= Null]





instance ToJSON DDecl where
    toJSON (DFun name args exp) = object ["DFun" .= (name, args, exp)]
    toJSON (DConstructor name tag arity) = object ["DConstructor" .= (name, tag, arity)]

instance ToJSON DExp where
    toJSON (DV lv) = object ["DV" .= lv]
    toJSON (DApp tail name exps) = object ["DApp" .= (tail, name, exps)]
    toJSON (DLet name a b) = object ["DLet" .= (name, a, b)]
    toJSON (DUpdate name exp) = object ["DUpdate" .= (name,exp)]
    toJSON (DProj exp i) = object ["DProj" .= (exp, i)]
    toJSON (DC lv i name exp) = object ["DC" .= (lv, i, name, exp)]
    toJSON (DCase ct exp alts) = object ["DCase" .= (ct, exp, alts)]
    toJSON (DChkCase exp alts) = object ["DChkCase" .= (exp, alts)]
    toJSON (DConst c) = object ["DConst" .= c]
    toJSON (DForeign fd ret exps) = object ["DForeign" .= (fd, ret, exps)]
    toJSON (DOp prim exps) = object ["DOp" .= (prim, exps)]
    toJSON DNothing = object ["DNothing" .= Null]
    toJSON (DError s) = object ["DError" .= s]

instance ToJSON DAlt where
    toJSON (DConCase i n ns exp) = object ["DConCase" .= (i, n, ns, exp)]
    toJSON (DConstCase c exp) = object ["DConstCase" .= (c, exp)]
    toJSON (DDefaultCase exp) = object ["DDefaultCase" .= exp]

instance ToJSON SDecl where
    toJSON (SFun name args i exp) = object ["SFun" .= (name, args, i, exp)]

instance ToJSON SExp where
    toJSON (SV lv) = object ["SV" .= lv]
    toJSON (SApp tail name exps) = object ["SApp" .= (tail, name, exps)]
    toJSON (SLet lv a b) = object ["SLet" .= (lv, a, b)]
    toJSON (SUpdate lv exp) = object ["SUpdate" .= (lv, exp)]
    toJSON (SProj lv i) = object ["SProj" .= (lv, i)]
    toJSON (SCon lv i name vars) = object ["SCon" .= (lv, i, name, vars)]
    toJSON (SCase ct lv alts) = object ["SCase" .= (ct, lv, alts)]
    toJSON (SChkCase lv alts) = object ["SChkCase" .= (lv, alts)]
    toJSON (SConst c) = object ["SConst" .= c]
    toJSON (SForeign fd ret exps) = object ["SForeign" .= (fd, ret, exps)]
    toJSON (SOp prim vars) = object ["SOp" .= (prim, vars)]
    toJSON SNothing = object ["SNothing" .= Null]
    toJSON (SError s) = object ["SError" .= s]

instance ToJSON SAlt where
    toJSON (SConCase i j n ns exp) = object ["SConCase" .= (i, j, n, ns, exp)]
    toJSON (SConstCase c exp) = object ["SConstCase" .= (c, exp)]
    toJSON (SDefaultCase exp) = object ["SDefaultCase" .= exp]

instance ToJSON BC where
    toJSON (ASSIGN r1 r2) = object ["ASSIGN" .= (r1, r2)]
    toJSON (ASSIGNCONST r c) = object ["ASSIGNCONST" .= (r, c)]
    toJSON (UPDATE r1 r2) = object ["UPDATE" .= (r1, r2)]
    toJSON (MKCON con mr i regs) = object ["MKCON" .= (con, mr, i, regs)]
    toJSON (CASE b r alts def) = object ["CASE" .= (b, r, alts, def)]
    toJSON (PROJECT r loc arity) = object ["PROJECT" .= (r, loc, arity)]
    toJSON (PROJECTINTO r1 r2 loc) = object ["PROJECTINTO" .= (r1, r2, loc)]
    toJSON (CONSTCASE r alts def) = object ["CONSTCASE" .= (r, alts, def)]
    toJSON (CALL name) = object ["CALL" .= name]
    toJSON (TAILCALL name) = object ["TAILCALL" .= name]
    toJSON (FOREIGNCALL r fd ret exps) = object ["FOREIGNCALL" .= (r, fd, ret, exps)]
    toJSON (SLIDE i) = object ["SLIDE" .= i]
    toJSON (RESERVE i) = object ["RESERVE" .= i]
    toJSON (ADDTOP i) = object ["ADDTOP" .= i]
    toJSON (TOPBASE i) = object ["TOPBASE" .= i]
    toJSON (BASETOP i) = object ["BASETOP" .= i]
    toJSON REBASE = object ["REBASE" .= Null]
    toJSON STOREOLD = object ["STOREOLD" .= Null]
    toJSON (OP r prim args) = object ["OP" .= (r, prim, args)]
    toJSON (NULL r) = object ["NULL" .= r]
    toJSON (ERROR s) = object ["ERROR" .= s]

instance ToJSON Reg where
    toJSON RVal = object ["RVal" .= Null]
    toJSON (T i) = object ["T" .= i]
    toJSON (L i) = object ["L" .= i]
    toJSON Tmp = object ["Tmp" .= Null]

instance ToJSON RigCount where
    toJSON r = object ["RigCount" .= show r]

instance ToJSON Totality where
    toJSON t = object ["Totality" .= show t]

instance ToJSON MetaInformation where
    toJSON m = object ["MetaInformation" .= show m]

instance ToJSON Def where
    toJSON (Function ty tm) = object ["Function" .= (ty, tm)]
    toJSON (TyDecl nm ty) = object ["TyDecl" .= (nm, ty)]
    toJSON (Operator ty n f) = Null -- Operator and CaseOp omits same values as in IBC.hs
    toJSON (CaseOp info ty argTy _ _ cdefs) = object ["CaseOp" .= (info, ty, argTy, cdefs)]

instance (ToJSON t) => ToJSON (TT t) where
    toJSON (P nt name term) = object ["P" .= (nt, name, term)]
    toJSON (V n) = object ["V" .= n]
    toJSON (Bind n b tt) = object ["Bind" .= (n, b, tt)]
    toJSON (App s t1 t2) = object ["App" .= (s, t1, t2)]
    toJSON (Constant c) = object ["Constant" .= c]
    toJSON (Proj tt n) = object ["Proj" .= (tt, n)]
    toJSON Erased = object ["Erased" .= Null]
    toJSON Impossible = object ["Impossible" .= Null]
    toJSON (Inferred tt) = object ["Inferred" .= tt]
    toJSON (TType u) = object ["TType" .= u]
    toJSON (UType u) = object ["UType" .= (show u)]

instance ToJSON UExp where
    toJSON (UVar src n) = object ["UVar" .= (src, n)]
    toJSON (UVal n) = object ["UVal" .= n]


instance (ToJSON t) => ToJSON (AppStatus t) where
    toJSON Complete = object ["Complete" .= Null]
    toJSON MaybeHoles = object ["MaybeHoles" .= Null]
    toJSON (Holes ns) = object ["Holes" .= ns]

instance (ToJSON t) => ToJSON (Binder t) where
    toJSON (Lam rc bty) = object ["Lam" .= (rc, bty)]
    toJSON (Pi c i t k) = object ["Pi" .= (c, i, t, k)]
    toJSON (Let t v) = object ["Let" .= (t, v)]
    toJSON (NLet t v) = object ["NLet" .= (t, v)]
    toJSON (Hole t) = object ["Hole" .= (t)]
    toJSON (GHole l ns t) = object ["GHole" .= (l, ns, t)]
    toJSON (Guess t v) = object ["Guess" .= (t, v)]
    toJSON (PVar rc t) = object ["PVar" .= (rc, t)]
    toJSON (PVTy t) = object ["PVTy" .= (t)]

instance ToJSON ImplicitInfo where
    toJSON (Impl a b c) = object ["Impl" .= (a, b, c)]

instance ToJSON NameType where
    toJSON Bound = object ["Bound" .= Null]
    toJSON Ref = object ["Ref" .= Null]
    toJSON (DCon a b c) = object ["DCon" .= (a, b, c)]
    toJSON (TCon a b) = object ["TCon" .= (a, b)]

instance ToJSON CaseDefs where
    toJSON (CaseDefs rt ct) = object ["Runtime" .= rt, "Compiletime" .= ct]

instance (ToJSON t) => ToJSON (SC' t) where
    toJSON (Case ct n alts) = object ["Case" .= (ct, n, alts)]
    toJSON (ProjCase t alts) = object ["ProjCase" .= (t, alts)]
    toJSON (STerm t) = object ["STerm" .= t]
    toJSON (UnmatchedCase s) = object ["UnmatchedCase" .= s]
    toJSON ImpossibleCase = object ["ImpossibleCase" .= Null]

instance (ToJSON t) => ToJSON (CaseAlt' t) where
    toJSON (ConCase n c ns sc) = object ["ConCase" .= (n, c, ns, sc)]
    toJSON (FnCase n ns sc) = object ["FnCase" .= (n, ns, sc)]
    toJSON (ConstCase c sc) = object ["ConstCase" .= (c, sc)]
    toJSON (SucCase n sc) = object ["SucCase" .= (n, sc)]
    toJSON (DefaultCase sc) = object ["DefaultCase" .=  sc]

instance ToJSON CaseInfo where
    toJSON (CaseInfo a b c) = object ["CaseInfo" .= (a, b, c)]

instance ToJSON Accessibility where
    toJSON a = object ["Accessibility" .= show a]

module IRTS.CodegenC (codegenC) where

import Idris.AbsSyntax
import IRTS.Bytecode
import IRTS.Lang
import IRTS.Simplified
import IRTS.System
import IRTS.CodegenCommon
import Idris.Core.TT
import Paths_idris
import Util.System

import Numeric
import Data.Char
import Data.List (intercalate)
import System.Process
import System.Exit
import System.IO
import System.Directory
import System.FilePath ((</>), (<.>))
import Control.Monad

codegenC :: [(Name, SDecl)] ->
            String -> -- output file name
            OutputType ->   -- generate executable if True, only .o if False
            [FilePath] -> -- include files
            String -> -- extra object files
            String -> -- extra compiler flags (libraries)
            String -> -- extra compiler flags (anything)
            DbgLevel ->
            IO ()
codegenC defs out exec incs objs libs flags dbg
    = do -- print defs
         let bc = map toBC defs
         let h = concatMap toDecl (map fst bc)
         let cc = concatMap (uncurry toC) bc
         d <- getDataDir
         mprog <- readFile (d </> "rts" </> "idris_main" <.> "c")
         let cout = headers incs ++ debug dbg ++ h ++ cc ++
                     (if (exec == Executable) then mprog else "")
         case exec of
           MavenProject -> putStrLn ("FAILURE: output type not supported")
           Raw -> writeFile out cout
           _ -> do
             (tmpn, tmph) <- tempfile
             hPutStr tmph cout
             hFlush tmph
             hClose tmph
             let useclang = False
             comp <- getCC
             libFlags <- getLibFlags
             incFlags <- getIncFlags
             let gcc = comp ++ " " ++
                       gccDbg dbg ++ " " ++
                       gccFlags ++
                       " -I. " ++ objs ++ " -x c " ++
                       (if (exec == Executable) then "" else " -c ") ++
                       " " ++ tmpn ++
                       " " ++ libFlags ++
                       " " ++ incFlags ++
                       " " ++ libs ++
                       " " ++ flags ++
                       " -o " ++ out
--              putStrLn gcc
             exit <- system gcc
             when (exit /= ExitSuccess) $
                putStrLn ("FAILURE: " ++ gcc)

headers xs =
  concatMap
    (\h -> "#include <" ++ h ++ ">\n")
    (xs ++ ["idris_rts.h", "idris_bitstring.h", "idris_stdfgn.h", "assert.h"])

debug TRACE = "#define IDRIS_TRACE\n\n"
debug _ = ""

-- We're using signed integers now. Make sure we get consistent semantics
-- out of them from gcc. See e.g. http://thiemonagel.de/2010/01/signed-integer-overflow/
gccFlags = " -fwrapv -fno-strict-overflow"

gccDbg DEBUG = "-g"
gccDbg TRACE = "-O2"
gccDbg _ = "-O2"

cname :: Name -> String
cname n = "_idris_" ++ concatMap cchar (showCG n)
  where cchar x | isAlpha x || isDigit x = [x]
                | otherwise = "_" ++ show (fromEnum x) ++ "_"

indent :: Int -> String
indent n = replicate (n*4) ' '

creg RVal = "RVAL"
creg (L i) = "LOC(" ++ show i ++ ")"
creg (T i) = "TOP(" ++ show i ++ ")"
creg Tmp = "REG1"

toDecl :: Name -> String
toDecl f = "void " ++ cname f ++ "(VM*, VAL*);\n"

toC :: Name -> [BC] -> String
toC f code
    = -- "/* " ++ show code ++ "*/\n\n" ++
      "void " ++ cname f ++ "(VM* vm, VAL* oldbase) {\n" ++
                 indent 1 ++ "INITFRAME;\n" ++
                 concatMap (bcc 1) code ++ "}\n\n"

showCStr :: String -> String
showCStr s = '"' : foldr ((++) . showChar) "\"" s
  where
    showChar :: Char -> String
    showChar '"'  = "\\\""
    showChar '\\' = "\\\\"
    showChar c
        -- Note: we need the double quotes around the codes because otherwise
        -- "\n3" would get encoded as "\x0a3", which is incorrect.
        -- Instead, we opt for "\x0a""3" and let the C compiler deal with it.
        | ord c < 0x10  = "\"\"\\x0" ++ showHex (ord c) "\"\""
        | ord c < 0x20  = "\"\"\\x"  ++ showHex (ord c) "\"\""
        | ord c < 0x7f  = [c]    -- 0x7f = \DEL
        | ord c < 0x100 = "\"\"\\x"  ++ showHex (ord c) "\"\""
        | otherwise = error $ "non-8-bit character in string literal: " ++ show c

bcc :: Int -> BC -> String
bcc i (ASSIGN l r) = indent i ++ creg l ++ " = " ++ creg r ++ ";\n"
bcc i (ASSIGNCONST l c)
    = indent i ++ creg l ++ " = " ++ mkConst c ++ ";\n"
  where
    mkConst (I i) = "MKINT(" ++ show i ++ ")"
    mkConst (BI i) | i < (2^30) = "MKINT(" ++ show i ++ ")"
                   | otherwise = "MKBIGC(vm,\"" ++ show i ++ "\")"
    mkConst (Fl f) = "MKFLOAT(vm, " ++ show f ++ ")"
    mkConst (Ch c) = "MKINT(" ++ show (fromEnum c) ++ ")"
    mkConst (Str s) = "MKSTR(vm, " ++ showCStr s ++ ")"
    mkConst (B8  x) = "idris_b8const(vm, "  ++ show x ++ ")"
    mkConst (B16 x) = "idris_b16const(vm, " ++ show x ++ ")"
    mkConst (B32 x) = "idris_b32const(vm, " ++ show x ++ ")"
    mkConst (B64 x) = "idris_b64const(vm, " ++ show x ++ ")"
    mkConst _ = "MKINT(42424242)"
bcc i (UPDATE l r) = indent i ++ creg l ++ " = " ++ creg r ++ ";\n"
bcc i (MKCON l tag args)
    = indent i ++ "allocCon(" ++ creg Tmp ++ ", vm, " ++ show tag ++ "," ++
         show (length args) ++ ", 0);\n" ++
      indent i ++ setArgs 0 args ++ "\n" ++
      indent i ++ creg l ++ " = " ++ creg Tmp ++ ";\n"

--         "MKCON(vm, " ++ creg l ++ ", " ++ show tag ++ ", " ++
--         show (length args) ++ concatMap showArg args ++ ");\n"
  where showArg r = ", " ++ creg r
        setArgs i [] = ""
        setArgs i (x : xs) = "SETARG(" ++ creg Tmp ++ ", " ++ show i ++ ", " ++ creg x ++
                             "); " ++ setArgs (i + 1) xs

bcc i (PROJECT l loc a) = indent i ++ "PROJECT(vm, " ++ creg l ++ ", " ++ show loc ++
                                      ", " ++ show a ++ ");\n"
bcc i (PROJECTINTO r t idx)
    = indent i ++ creg r ++ " = GETARG(" ++ creg t ++ ", " ++ show idx ++ ");\n"
bcc i (CASE True r code def)
    | length code < 4 = showCase i def code
  where
    showCode :: Int -> [BC] -> String
    showCode i bc = "{\n" ++ indent i ++ concatMap (bcc (i + 1)) bc ++
                    indent i ++ "}\n"

    showCase :: Int -> Maybe [BC] -> [(Int, [BC])] -> String
    showCase i Nothing [(t, c)] = showCode i c
    showCase i (Just def) [] = showCode i def
    showCase i def ((t, c) : cs)
        = "if (CTAG(" ++ creg r ++ ") == " ++ show t ++ ") " ++ showCode i c
           ++ "else " ++ showCase i def cs

bcc i (CASE safe r code def)
    = indent i ++ "switch(" ++ ctag safe ++ "(" ++ creg r ++ ")) {\n" ++
      concatMap (showCase i) code ++
      showDef i def ++
      indent i ++ "}\n"
  where
    ctag True = "CTAG"
    ctag False = "TAG"

    showCase i (t, bc) = indent i ++ "case " ++ show t ++ ":\n"
                         ++ concatMap (bcc (i+1)) bc ++ indent (i + 1) ++ "break;\n"
    showDef i Nothing = ""
    showDef i (Just c) = indent i ++ "default:\n"
                         ++ concatMap (bcc (i+1)) c ++ indent (i + 1) ++ "break;\n"
bcc i (CONSTCASE r code def)
   | intConsts code
--      = indent i ++ "switch(GETINT(" ++ creg r ++ ")) {\n" ++
--        concatMap (showCase i) code ++
--        showDef i def ++
--        indent i ++ "}\n"
     = concatMap (iCase (creg r)) code ++
       indent i ++ "{\n" ++ showDefS i def ++ indent i ++ "}\n"
   | strConsts code
     = concatMap (strCase ("GETSTR(" ++ creg r ++ ")")) code ++
       indent i ++ "{\n" ++ showDefS i def ++ indent i ++ "}\n"
   | bigintConsts code
     = concatMap (biCase (creg r)) code ++
       indent i ++ "{\n" ++ showDefS i def ++ indent i ++ "}\n"
   | otherwise = error $ "Can't happen: Can't compile const case " ++ show code
  where
    intConsts ((I _, _ ) : _) = True
    intConsts ((Ch _, _ ) : _) = True
    intConsts _ = False

    bigintConsts ((BI _, _ ) : _) = True
    bigintConsts _ = False

    strConsts ((Str _, _ ) : _) = True
    strConsts _ = False

    strCase sv (s, bc) =
        indent i ++ "if (strcmp(" ++ sv ++ ", " ++ show s ++ ") == 0) {\n" ++
           concatMap (bcc (i+1)) bc ++ indent i ++ "} else\n"
    biCase bv (BI b, bc) =
        indent i ++ "if (bigEqConst(" ++ bv ++ ", " ++ show b ++ ")) {\n"
           ++ concatMap (bcc (i+1)) bc ++ indent i ++ "} else\n"
    iCase v (I b, bc) =
        indent i ++ "if (GETINT(" ++ v ++ ") == " ++ show b ++ ") {\n"
           ++ concatMap (bcc (i+1)) bc ++ indent i ++ "} else\n"
    iCase v (Ch b, bc) =
        indent i ++ "if (GETINT(" ++ v ++ ") == " ++ show (fromEnum b) ++ ") {\n"
           ++ concatMap (bcc (i+1)) bc ++ indent i ++ "} else\n"

    showCase i (t, bc) = indent i ++ "case " ++ show t ++ ":\n"
                         ++ concatMap (bcc (i+1)) bc ++
                            indent (i + 1) ++ "break;\n"
    showDef i Nothing = ""
    showDef i (Just c) = indent i ++ "default:\n"
                         ++ concatMap (bcc (i+1)) c ++
                            indent (i + 1) ++ "break;\n"
    showDefS i Nothing = ""
    showDefS i (Just c) = concatMap (bcc (i+1)) c

bcc i (CALL n) = indent i ++ "CALL(" ++ cname n ++ ");\n"
bcc i (TAILCALL n) = indent i ++ "TAILCALL(" ++ cname n ++ ");\n"
bcc i (SLIDE n) = indent i ++ "SLIDE(vm, " ++ show n ++ ");\n"
bcc i REBASE = indent i ++ "REBASE;\n"
bcc i (RESERVE 0) = ""
bcc i (RESERVE n) = indent i ++ "RESERVE(" ++ show n ++ ");\n"
bcc i (ADDTOP 0) = ""
bcc i (ADDTOP n) = indent i ++ "ADDTOP(" ++ show n ++ ");\n"
bcc i (TOPBASE n) = indent i ++ "TOPBASE(" ++ show n ++ ");\n"
bcc i (BASETOP n) = indent i ++ "BASETOP(" ++ show n ++ ");\n"
bcc i STOREOLD = indent i ++ "STOREOLD;\n"
bcc i (OP l fn args) = indent i ++ doOp (creg l ++ " = ") fn args ++ ";\n"
bcc i (FOREIGNCALL l LANG_C rty fn args)
      = indent i ++
        c_irts rty (creg l ++ " = ")
                   (fn ++ "(" ++ showSep "," (map fcall args) ++ ")") ++ ";\n"
    where fcall (t, arg) = irts_c t (creg arg)
bcc i (NULL r) = indent i ++ creg r ++ " = NULL;\n" -- clear, so it'll be GCed
bcc i (ERROR str) = indent i ++ "fprintf(stderr, " ++ show str ++ "); assert(0); exit(-1);"
-- bcc i _ = indent i ++ "// not done yet\n"



c_irts (FArith (ATInt ITNative)) l x = l ++ "MKINT((i_int)(" ++ x ++ "))"
c_irts (FArith (ATInt ITChar))  l x = c_irts (FArith (ATInt ITNative)) l x
c_irts (FArith (ATInt (ITFixed ity))) l x
    = l ++ "idris_b" ++ show (nativeTyWidth ity) ++ "const(vm, " ++ x ++ ")"
c_irts FString l x = l ++ "MKSTR(vm, " ++ x ++ ")"
c_irts FUnit l x = x
c_irts FPtr l x = l ++ "MKPTR(vm, " ++ x ++ ")"
c_irts (FArith ATFloat) l x = l ++ "MKFLOAT(vm, " ++ x ++ ")"
c_irts FAny l x = l ++ x

irts_c (FArith (ATInt ITNative)) x = "GETINT(" ++ x ++ ")"
irts_c (FArith (ATInt ITChar)) x = irts_c (FArith (ATInt ITNative)) x
irts_c (FArith (ATInt (ITFixed ity))) x
    = "(" ++ x ++ "->info.bits" ++ show (nativeTyWidth ity) ++ ")"
irts_c FString x = "GETSTR(" ++ x ++ ")"
irts_c FUnit x = x
irts_c FPtr x = "GETPTR(" ++ x ++ ")"
irts_c (FArith ATFloat) x = "GETFLOAT(" ++ x ++ ")"
irts_c FAny x = x

bitOp v op ty args = v ++ "idris_b" ++ show (nativeTyWidth ty) ++ op ++ "(vm, " ++ intercalate ", " (map creg args) ++ ")"

bitCoerce v op input output arg
    = v ++ "idris_b" ++ show (nativeTyWidth input) ++ op ++ show (nativeTyWidth output) ++ "(vm, " ++ creg arg ++ ")"

signedTy :: NativeTy -> String
signedTy t = "int" ++ show (nativeTyWidth t) ++ "_t"

doOp v (LPlus (ATInt ITNative)) [l, r] = v ++ "ADD(" ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LMinus (ATInt ITNative)) [l, r] = v ++ "INTOP(-," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LTimes (ATInt ITNative)) [l, r] = v ++ "MULT(" ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LUDiv ITNative) [l, r] = v ++ "UINTOP(/," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSDiv (ATInt ITNative)) [l, r] = v ++ "INTOP(/," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LURem ITNative) [l, r] = v ++ "UINTOP(%," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSRem (ATInt ITNative)) [l, r] = v ++ "INTOP(%," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LAnd ITNative) [l, r] = v ++ "INTOP(&," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LOr ITNative) [l, r] = v ++ "INTOP(|," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LXOr ITNative) [l, r] = v ++ "INTOP(^," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSHL ITNative) [l, r] = v ++ "INTOP(<<," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LLSHR ITNative) [l, r] = v ++ "UINTOP(>>," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LASHR ITNative) [l, r] = v ++ "INTOP(>>," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LCompl ITNative) [x] = v ++ "INTOP(~," ++ creg x ++ ")"
doOp v (LEq (ATInt ITNative)) [l, r] = v ++ "INTOP(==," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSLt (ATInt ITNative)) [l, r] = v ++ "INTOP(<," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSLe (ATInt ITNative)) [l, r] = v ++ "INTOP(<=," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSGt (ATInt ITNative)) [l, r] = v ++ "INTOP(>," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSGe (ATInt ITNative)) [l, r] = v ++ "INTOP(>=," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LLt ITNative) [l, r] = v ++ "UINTOP(<," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LLe ITNative) [l, r] = v ++ "UINTOP(<=," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LGt ITNative) [l, r] = v ++ "UINTOP(>," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LGe ITNative) [l, r] = v ++ "UINTOP(>=," ++ creg l ++ ", " ++ creg r ++ ")"

doOp v (LPlus (ATInt ITChar)) [l, r] = doOp v (LPlus (ATInt ITNative)) [l, r]
doOp v (LMinus (ATInt ITChar)) [l, r] = doOp v (LMinus (ATInt ITNative)) [l, r]
doOp v (LTimes (ATInt ITChar)) [l, r] = doOp v (LTimes (ATInt ITNative)) [l, r]
doOp v (LUDiv ITChar) [l, r] = doOp v (LUDiv ITNative) [l, r]
doOp v (LSDiv (ATInt ITChar)) [l, r] = doOp v (LSDiv (ATInt ITNative)) [l, r]
doOp v (LURem ITChar) [l, r] = doOp v (LURem ITNative) [l, r]
doOp v (LSRem (ATInt ITChar)) [l, r] = doOp v (LSRem (ATInt ITNative)) [l, r]
doOp v (LAnd ITChar) [l, r] = doOp v (LAnd ITNative) [l, r]
doOp v (LOr ITChar) [l, r] = doOp v (LOr ITNative) [l, r]
doOp v (LXOr ITChar) [l, r] = doOp v (LXOr ITNative) [l, r]
doOp v (LSHL ITChar) [l, r] = doOp v (LSHL ITNative) [l, r]
doOp v (LLSHR ITChar) [l, r] = doOp v (LLSHR ITNative) [l, r]
doOp v (LASHR ITChar) [l, r] = doOp v (LASHR ITNative) [l, r]
doOp v (LCompl ITChar) [x] = doOp v (LCompl ITNative) [x]
doOp v (LEq (ATInt ITChar)) [l, r] = doOp v (LEq (ATInt ITNative)) [l, r]
doOp v (LSLt (ATInt ITChar)) [l, r] = doOp v (LSLt (ATInt ITNative)) [l, r]
doOp v (LSLe (ATInt ITChar)) [l, r] = doOp v (LSLe (ATInt ITNative)) [l, r]
doOp v (LSGt (ATInt ITChar)) [l, r] = doOp v (LSGt (ATInt ITNative)) [l, r]
doOp v (LSGe (ATInt ITChar)) [l, r] = doOp v (LSGe (ATInt ITNative)) [l, r]
doOp v (LLt ITChar) [l, r] = doOp v (LLt ITNative) [l, r]
doOp v (LLe ITChar) [l, r] = doOp v (LLe ITNative) [l, r]
doOp v (LGt ITChar) [l, r] = doOp v (LGt ITNative) [l, r]
doOp v (LGe ITChar) [l, r] = doOp v (LGe ITNative) [l, r]

doOp v (LPlus ATFloat) [l, r] = v ++ "FLOATOP(+," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LMinus ATFloat) [l, r] = v ++ "FLOATOP(-," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LTimes ATFloat) [l, r] = v ++ "FLOATOP(*," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSDiv ATFloat) [l, r] = v ++ "FLOATOP(/," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LEq ATFloat) [l, r] = v ++ "FLOATBOP(==," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSLt ATFloat) [l, r] = v ++ "FLOATBOP(<," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSLe ATFloat) [l, r] = v ++ "FLOATBOP(<=," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSGt ATFloat) [l, r] = v ++ "FLOATBOP(>," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSGe ATFloat) [l, r] = v ++ "FLOATBOP(>=," ++ creg l ++ ", " ++ creg r ++ ")"

doOp v (LIntFloat ITBig) [x] = v ++ "idris_castBigFloat(vm, " ++ creg x ++ ")"
doOp v (LFloatInt ITBig) [x] = v ++ "idris_castFloatBig(vm, " ++ creg x ++ ")"
doOp v (LPlus (ATInt ITBig)) [l, r] = v ++ "idris_bigPlus(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LMinus (ATInt ITBig)) [l, r] = v ++ "idris_bigMinus(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LTimes (ATInt ITBig)) [l, r] = v ++ "idris_bigTimes(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSDiv (ATInt ITBig)) [l, r] = v ++ "idris_bigDivide(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSRem (ATInt ITBig)) [l, r] = v ++ "idris_bigMod(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LEq (ATInt ITBig)) [l, r] = v ++ "idris_bigEq(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSLt (ATInt ITBig)) [l, r] = v ++ "idris_bigLt(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSLe (ATInt ITBig)) [l, r] = v ++ "idris_bigLe(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSGt (ATInt ITBig)) [l, r] = v ++ "idris_bigGt(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSGe (ATInt ITBig)) [l, r] = v ++ "idris_bigGe(vm, " ++ creg l ++ ", " ++ creg r ++ ")"

doOp v LStrConcat [l,r] = v ++ "idris_concat(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LStrLt [l,r] = v ++ "idris_strlt(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LStrEq [l,r] = v ++ "idris_streq(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LStrLen [x] = v ++ "idris_strlen(vm, " ++ creg x ++ ")"

doOp v (LIntFloat ITNative) [x] = v ++ "idris_castIntFloat(" ++ creg x ++ ")"
doOp v (LFloatInt ITNative) [x] = v ++ "idris_castFloatInt(" ++ creg x ++ ")"
doOp v (LSExt ITNative ITBig) [x] = v ++ "idris_castIntBig(vm, " ++ creg x ++ ")"
doOp v (LTrunc ITBig ITNative) [x] = v ++ "idris_castBigInt(vm, " ++ creg x ++ ")"
doOp v (LStrInt ITBig) [x] = v ++ "idris_castStrBig(vm, " ++ creg x ++ ")"
doOp v (LIntStr ITBig) [x] = v ++ "idris_castBigStr(vm, " ++ creg x ++ ")"
doOp v (LIntStr ITNative) [x] = v ++ "idris_castIntStr(vm, " ++ creg x ++ ")"
doOp v (LStrInt ITNative) [x] = v ++ "idris_castStrInt(vm, " ++ creg x ++ ")"
doOp v LFloatStr [x] = v ++ "idris_castFloatStr(vm, " ++ creg x ++ ")"
doOp v LStrFloat [x] = v ++ "idris_castStrFloat(vm, " ++ creg x ++ ")"

doOp v LReadStr [x] = v ++ "idris_readStr(vm, GETPTR(" ++ creg x ++ "))"
doOp _ LPrintNum [x] = "printf(\"%ld\\n\", GETINT(" ++ creg x ++ "))"
doOp _ LPrintStr [x] = "fputs(GETSTR(" ++ creg x ++ "), stdout)"

doOp v (LSLt (ATInt (ITFixed ty))) [x, y] = bitOp v "SLt" ty [x, y]
doOp v (LSLe (ATInt (ITFixed ty))) [x, y] = bitOp v "SLte" ty [x, y]
doOp v (LEq (ATInt (ITFixed ty))) [x, y] = bitOp v "Eq" ty [x, y]
doOp v (LSGe (ATInt (ITFixed ty))) [x, y] = bitOp v "SGte" ty [x, y]
doOp v (LSGt (ATInt (ITFixed ty))) [x, y] = bitOp v "SGt" ty [x, y]
doOp v (LLt (ITFixed ty)) [x, y] = bitOp v "Lt" ty [x, y]
doOp v (LLe (ITFixed ty)) [x, y] = bitOp v "Lte" ty [x, y]
doOp v (LGe (ITFixed ty)) [x, y] = bitOp v "Gte" ty [x, y]
doOp v (LGt (ITFixed ty)) [x, y] = bitOp v "Gt" ty [x, y]

doOp v (LSHL (ITFixed ty)) [x, y] = bitOp v "Shl" ty [x, y]
doOp v (LLSHR (ITFixed ty)) [x, y] = bitOp v "LShr" ty [x, y]
doOp v (LASHR (ITFixed ty)) [x, y] = bitOp v "AShr" ty [x, y]
doOp v (LAnd (ITFixed ty)) [x, y] = bitOp v "And" ty [x, y]
doOp v (LOr (ITFixed ty)) [x, y] = bitOp v "Or" ty [x, y]
doOp v (LXOr (ITFixed ty)) [x, y] = bitOp v "Xor" ty [x, y]
doOp v (LCompl (ITFixed ty)) [x] = bitOp v "Compl" ty [x]

doOp v (LPlus (ATInt (ITFixed ty))) [x, y] = bitOp v "Plus" ty [x, y]
doOp v (LMinus (ATInt (ITFixed ty))) [x, y] = bitOp v "Minus" ty [x, y]
doOp v (LTimes (ATInt (ITFixed ty))) [x, y] = bitOp v "Times" ty [x, y]
doOp v (LUDiv (ITFixed ty)) [x, y] = bitOp v "UDiv" ty [x, y]
doOp v (LSDiv (ATInt (ITFixed ty))) [x, y] = bitOp v "SDiv" ty [x, y]
doOp v (LURem (ITFixed ty)) [x, y] = bitOp v "URem" ty [x, y]
doOp v (LSRem (ATInt (ITFixed ty))) [x, y] = bitOp v "SRem" ty [x, y]

doOp v (LSExt (ITFixed from) ITBig) [x]
    = v ++ "MKBIGSI(vm, (" ++ signedTy from ++ ")" ++ creg x ++ "->info.bits" ++ show (nativeTyWidth from) ++ ")"
doOp v (LSExt ITNative (ITFixed to)) [x]
    = v ++ "idris_b" ++ show (nativeTyWidth to) ++ "const(vm, GETINT(" ++ creg x ++ "))"
doOp v (LSExt ITChar (ITFixed to)) [x]
    = doOp v (LSExt ITNative (ITFixed to)) [x]
doOp v (LSExt (ITFixed from) ITNative) [x]
    = v ++ "MKINT((i_int)((" ++ signedTy from ++ ")" ++ creg x ++ "->info.bits" ++ show (nativeTyWidth from) ++ "))"
doOp v (LSExt (ITFixed from) ITChar) [x]
    = doOp v (LSExt (ITFixed from) ITNative) [x]
doOp v (LSExt (ITFixed from) (ITFixed to)) [x]
    | nativeTyWidth from < nativeTyWidth to = bitCoerce v "S" from to x
doOp v (LZExt ITNative (ITFixed to)) [x]
    = v ++ "idris_b" ++ show (nativeTyWidth to) ++ "const(vm, (uintptr_t)GETINT(" ++ creg x ++ ")"
doOp v (LZExt ITChar (ITFixed to)) [x]
    = doOp v (LZExt ITNative (ITFixed to)) [x]
doOp v (LZExt (ITFixed from) ITNative) [x]
    = v ++ "MKINT((i_int)" ++ creg x ++ "->info.bits" ++ show (nativeTyWidth from) ++ ")"
doOp v (LZExt (ITFixed from) ITChar) [x]
    = doOp v (LZExt (ITFixed from) ITNative) [x]
doOp v (LZExt (ITFixed from) ITBig) [x]
    = v ++ "MKBIGUI(vm, " ++ creg x ++ "->info.bits" ++ show (nativeTyWidth from) ++ ")"
doOp v (LZExt ITNative ITBig) [x]
    = v ++ "MKBIGUI(vm, (uintptr_t)GETINT(" ++ creg x ++ "))"
doOp v (LZExt (ITFixed from) (ITFixed to)) [x]
    | nativeTyWidth from < nativeTyWidth to = bitCoerce v "Z" from to x
doOp v (LTrunc ITNative (ITFixed to)) [x]
    = v ++ "idris_b" ++ show (nativeTyWidth to) ++ "const(vm, GETINT(" ++ creg x ++ "))"
doOp v (LTrunc ITChar (ITFixed to)) [x]
    = doOp v (LTrunc ITNative (ITFixed to)) [x]
doOp v (LTrunc (ITFixed from) ITNative) [x]
    = v ++ "MKINT((i_int)" ++ creg x ++ "->info.bits" ++ show (nativeTyWidth from) ++ ")"
doOp v (LTrunc (ITFixed from) ITChar) [x]
    = doOp v (LTrunc (ITFixed from) ITNative) [x]
doOp v (LTrunc ITBig (ITFixed to)) [x]
    = v ++ "idris_b" ++ show (nativeTyWidth to) ++ "const(vm, ISINT(" ++ creg x ++ ") ? GETINT(" ++ creg x ++ ") : mpz_get_ui(GETMPZ(" ++ creg x ++ ")))"
doOp v (LTrunc (ITFixed from) (ITFixed to)) [x]
    | nativeTyWidth from > nativeTyWidth to = bitCoerce v "T" from to x

doOp v LFExp [x] = v ++ flUnOp "exp" (creg x)
doOp v LFLog [x] = v ++ flUnOp "log" (creg x)
doOp v LFSin [x] = v ++ flUnOp "sin" (creg x)
doOp v LFCos [x] = v ++ flUnOp "cos" (creg x)
doOp v LFTan [x] = v ++ flUnOp "tan" (creg x)
doOp v LFASin [x] = v ++ flUnOp "asin" (creg x)
doOp v LFACos [x] = v ++ flUnOp "acos" (creg x)
doOp v LFATan [x] = v ++ flUnOp "atan" (creg x)
doOp v LFSqrt [x] = v ++ flUnOp "sqrt" (creg x)
doOp v LFFloor [x] = v ++ flUnOp "floor" (creg x)
doOp v LFCeil [x] = v ++ flUnOp "ceil" (creg x)

doOp v LStrHead [x] = v ++ "idris_strHead(vm, " ++ creg x ++ ")"
doOp v LStrTail [x] = v ++ "idris_strTail(vm, " ++ creg x ++ ")"
doOp v LStrCons [x, y] = v ++ "idris_strCons(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LStrIndex [x, y] = v ++ "idris_strIndex(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LStrRev [x] = v ++ "idris_strRev(vm, " ++ creg x ++ ")"

doOp v LStdIn [] = v ++ "MKPTR(vm, stdin)"
doOp v LStdOut [] = v ++ "MKPTR(vm, stdout)"
doOp v LStdErr [] = v ++ "MKPTR(vm, stderr)"

doOp v LFork [x] = v ++ "MKPTR(vm, vmThread(vm, " ++ cname (sMN 0 "EVAL") ++ ", " ++ creg x ++ "))"
doOp v LPar [x] = v ++ creg x -- "MKPTR(vm, vmThread(vm, " ++ cname (MN 0 "EVAL") ++ ", " ++ creg x ++ "))"
doOp v LVMPtr [] = v ++ "MKPTR(vm, vm)"
doOp v LNullPtr [] = v ++ "MKPTR(vm, NULL)"
doOp v (LChInt ITNative) args = v ++ creg (last args)
doOp v (LChInt ITChar) args = doOp v (LChInt ITNative) args
doOp v (LIntCh ITNative) args = v ++ creg (last args)
doOp v (LIntCh ITChar) args = doOp v (LIntCh ITNative) args
doOp v LNoOp args = v ++ creg (last args)
doOp _ op _ = "FAIL /* " ++ show op ++ " */"

flUnOp :: String -> String -> String
flUnOp name val = "MKFLOAT(vm, " ++ name ++ "(GETFLOAT(" ++ val ++ ")))"

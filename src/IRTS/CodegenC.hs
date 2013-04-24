module IRTS.CodegenC (codegenC) where

import Idris.AbsSyntax
import IRTS.Bytecode
import IRTS.Lang
import IRTS.Simplified
import IRTS.CodegenCommon
import Core.TT
import Paths_idris
import Util.System

import Data.Char
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
            String -> -- extra compiler flags
            DbgLevel ->
            IO ()
codegenC defs out exec incs objs libs dbg
    = do -- print defs
         let bc = map toBC defs
         let h = concatMap toDecl (map fst bc)
         let cc = concatMap (uncurry toC) bc
         d <- getDataDir
         mprog <- readFile (d </> "rts" </> "idris_main" <.> "c")
         let cout = headers incs ++ debug dbg ++ h ++ cc ++ 
                     (if (exec == Executable) then mprog else "")
         case exec of
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
                       gccDbg dbg ++
                       " -I. " ++ objs ++ " -x c " ++
                       (if (exec == Executable) then "" else " -c ") ++
                       " " ++ tmpn ++
                       " " ++ libFlags ++
                       " " ++ incFlags ++
                       " " ++ libs ++
                       " -o " ++ out
--              putStrLn gcc
             exit <- system gcc
             when (exit /= ExitSuccess) $
                putStrLn ("FAILURE: " ++ gcc)

headers xs =
  concatMap
    (\h -> "#include <" ++ h ++ ">\n")
    (xs ++ ["idris_rts.h", "idris_bitstring.h", "idris_stdfgn.h", "gmp.h", "assert.h"])

debug TRACE = "#define IDRIS_TRACE\n\n"
debug _ = ""

gccDbg DEBUG = "-g"
gccDbg TRACE = "-O2"
gccDbg _ = "-O2"

cname :: Name -> String
cname n = "_idris_" ++ concatMap cchar (show n)
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
    mkConst (Str s) = "MKSTR(vm, " ++ show s ++ ")"
    mkConst (B8 b) = "MKB8(vm, " ++ show b ++")"
    mkConst (B16 b) = "MKB16(vm, " ++ show b ++ ")"
    mkConst (B32 b) = "MKB32(vm, " ++ show b ++ ")"
    mkConst (B64 b) = "MKB64(vm, " ++ show b ++ ")"
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
        indent i ++ "if (GETINT(" ++ v ++ ") == " ++ show b ++ ") {\n"
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

c_irts FInt l x = l ++ "MKINT((i_int)(" ++ x ++ "))"
c_irts FChar l x = l ++ "MKINT((i_int)(" ++ x ++ "))"
c_irts FString l x = l ++ "MKSTR(vm, " ++ x ++ ")"
c_irts FUnit l x = x
c_irts FPtr l x = l ++ "MKPTR(vm, " ++ x ++ ")"
c_irts FDouble l x = l ++ "MKFLOAT(vm, " ++ x ++ ")"
c_irts FAny l x = l ++ x

irts_c FInt x = "GETINT(" ++ x ++ ")"
irts_c FChar x = "GETINT(" ++ x ++ ")"
irts_c FString x = "GETSTR(" ++ x ++ ")"
irts_c FUnit x = x
irts_c FPtr x = "GETPTR(" ++ x ++ ")"
irts_c FDouble x = "GETFLOAT(" ++ x ++ ")"
irts_c FAny x = x

doOp v LPlus [l, r] = v ++ "ADD(" ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LMinus [l, r] = v ++ "INTOP(-," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LTimes [l, r] = v ++ "MULT(" ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LDiv [l, r] = v ++ "INTOP(/," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LMod [l, r] = v ++ "INTOP(%," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LAnd [l, r] = v ++ "INTOP(&," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LOr [l, r] = v ++ "INTOP(|," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LXOr [l, r] = v ++ "INTOP(^," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LSHL [l, r] = v ++ "INTOP(<<," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LSHR [l, r] = v ++ "INTOP(>>," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LCompl [x] = v ++ "INTOP(~," ++ creg x ++ ")"
doOp v LEq [l, r] = v ++ "INTOP(==," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LLt [l, r] = v ++ "INTOP(<," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LLe [l, r] = v ++ "INTOP(<=," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LGt [l, r] = v ++ "INTOP(>," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LGe [l, r] = v ++ "INTOP(>=," ++ creg l ++ ", " ++ creg r ++ ")"

doOp v LFPlus [l, r] = v ++ "FLOATOP(+," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LFMinus [l, r] = v ++ "FLOATOP(-," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LFTimes [l, r] = v ++ "FLOATOP(*," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LFDiv [l, r] = v ++ "FLOATOP(/," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LFEq [l, r] = v ++ "FLOATBOP(==," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LFLt [l, r] = v ++ "FLOATBOP(<," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LFLe [l, r] = v ++ "FLOATBOP(<=," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LFGt [l, r] = v ++ "FLOATBOP(>," ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LFGe [l, r] = v ++ "FLOATBOP(>=," ++ creg l ++ ", " ++ creg r ++ ")"

doOp v LBPlus [l, r] = v ++ "idris_bigPlus(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LBMinus [l, r] = v ++ "idris_bigMinus(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LBDec [l] = v ++ "idris_bigMinus(vm, " ++ creg l ++ ", MKINT(1))"
doOp v LBTimes [l, r] = v ++ "idris_bigTimes(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LBDiv [l, r] = v ++ "idris_bigDivide(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LBMod [l, r] = v ++ "idris_bigMod(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LBEq [l, r] = v ++ "idris_bigEq(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LBLt [l, r] = v ++ "idris_bigLt(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LBLe [l, r] = v ++ "idris_bigLe(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LBGt [l, r] = v ++ "idris_bigGt(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LBGe [l, r] = v ++ "idris_bigGe(vm, " ++ creg l ++ ", " ++ creg r ++ ")"

doOp v LStrConcat [l,r] = v ++ "idris_concat(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LStrLt [l,r] = v ++ "idris_strlt(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LStrEq [l,r] = v ++ "idris_streq(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LStrLen [x] = v ++ "idris_strlen(vm, " ++ creg x ++ ")"

doOp v LIntFloat [x] = v ++ "idris_castIntFloat(" ++ creg x ++ ")"
doOp v LFloatInt [x] = v ++ "idris_castFloatInt(" ++ creg x ++ ")"
doOp v LIntStr [x] = v ++ "idris_castIntStr(vm, " ++ creg x ++ ")"
doOp v LStrInt [x] = v ++ "idris_castStrInt(vm, " ++ creg x ++ ")"
doOp v LIntBig [x] = v ++ "idris_castIntBig(vm, " ++ creg x ++ ")"
doOp v LBigInt [x] = v ++ "idris_castBigInt(vm, " ++ creg x ++ ")"
doOp v LStrBig [x] = v ++ "idris_castStrBig(vm, " ++ creg x ++ ")"
doOp v LBigStr [x] = v ++ "idris_castBigStr(vm, " ++ creg x ++ ")"
doOp v LFloatStr [x] = v ++ "idris_castFloatStr(vm, " ++ creg x ++ ")"
doOp v LStrFloat [x] = v ++ "idris_castStrFloat(vm, " ++ creg x ++ ")"

doOp v LReadStr [x] = v ++ "idris_readStr(vm, GETPTR(" ++ creg x ++ "))"
doOp _ LPrintNum [x] = "printf(\"%ld\\n\", GETINT(" ++ creg x ++ "))"
doOp _ LPrintStr [x] = "fputs(GETSTR(" ++ creg x ++ "), stdout)"

doOp v LIntB8 [x] = v ++ "idris_b8(vm, " ++ creg x ++ ")"
doOp v LIntB16 [x] = v ++ "idris_b16(vm, " ++ creg x ++ ")"
doOp v LIntB32 [x] = v ++ "idris_b32(vm, " ++ creg x ++ ")"
doOp v LIntB64 [x] = v ++ "idris_b64(vm, " ++ creg x ++ ")"

doOp v LB32Int [x] = v ++ "idris_castB32Int(vm, " ++ creg x ++ ")"

doOp v LB8Lt [x, y] = v ++ "idris_b8Lt(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8Lte [x, y] = v ++ "idris_b8Lte(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8Eq [x, y] = v ++ "idris_b8Eq(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8Gte [x, y] = v ++ "idris_b8Gte(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8Gt [x, y] = v ++ "idris_b8Gt(vm, " ++ creg x ++ "," ++ creg y ++ ")"

doOp v LB8Shl [x, y] = v ++ "idris_b8Shl(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8LShr [x, y] = v ++ "idris_b8Shr(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8AShr [x, y] = v ++ "idris_b8AShr(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8And [x, y] = v ++ "idris_b8And(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8Or [x, y] = v ++ "idris_b8Or(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8Xor [x, y] = v ++ "idris_b8Xor(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8Compl [x] = v ++ "idris_b8Compl(vm, " ++ creg x ++ ")"

doOp v LB8Plus [x, y] = v ++ "idris_b8Plus(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8Minus [x, y] = v ++ "idris_b8Minus(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8Times [x, y] = v ++ "idris_b8Times(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8UDiv [x, y] = v ++ "idris_b8UDiv(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8SDiv [x, y] = v ++ "idris_b8SDiv(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8URem [x, y] = v ++ "idris_b8URem(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB8SRem [x, y] = v ++ "idris_b8SRem(vm, " ++ creg x ++ "," ++ creg y ++ ")"

doOp v LB8Z16 [x] = v ++ "idris_b8Z16(vm, " ++ creg x ++ ")"
doOp v LB8Z32 [x] = v ++ "idris_b8Z32(vm, " ++ creg x ++ ")"
doOp v LB8Z64 [x] = v ++ "idris_b8Z64(vm, " ++ creg x ++ ")"
doOp v LB8S16 [x] = v ++ "idris_b8S16(vm, " ++ creg x ++ ")"
doOp v LB8S32 [x] = v ++ "idris_b8S32(vm, " ++ creg x ++ ")"
doOp v LB8S64 [x] = v ++ "idris_b8S64(vm, " ++ creg x ++ ")"

doOp v LB16Lt [x, y] = v ++ "idris_b16Lt(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16Lte [x, y] = v ++ "idris_b16Lte(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16Eq [x, y] = v ++ "idris_b16Eq(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16Gte [x, y] = v ++ "idris_b16Gte(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16Gt [x, y] = v ++ "idris_b16Gt(vm, " ++ creg x ++ "," ++ creg y ++ ")"

doOp v LB16Shl [x, y] = v ++ "idris_b16Shl(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16LShr [x, y] = v ++ "idris_b16Shr(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16AShr [x, y] = v ++ "idris_b16AShr(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16And [x, y] = v ++ "idris_b16And(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16Or [x, y] = v ++ "idris_b16Or(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16Xor [x, y] = v ++ "idris_b16Xor(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16Compl [x] = v ++ "idris_b16Compl(vm, " ++ creg x ++ ")"

doOp v LB16Plus [x, y] =
  v ++ "idris_b16Plus(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16Minus [x, y] =
  v ++ "idris_b16Minus(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16Times [x, y] =
  v ++ "idris_b16Times(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16UDiv [x, y] =
  v ++ "idris_b16UDiv(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16SDiv [x, y] =
  v ++ "idris_b16SDiv(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16URem [x, y] =
  v ++ "idris_b16URem(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB16SRem [x, y] =
  v ++ "idris_b16SRem(vm, " ++ creg x ++ "," ++ creg y ++ ")"

doOp v LB16Z32 [x] = v ++ "idris_b16Z32(vm, " ++ creg x ++ ")"
doOp v LB16Z64 [x] = v ++ "idris_b16Z64(vm, " ++ creg x ++ ")"
doOp v LB16S32 [x] = v ++ "idris_b16S32(vm, " ++ creg x ++ ")"
doOp v LB16S64 [x] = v ++ "idris_b16S64(vm, " ++ creg x ++ ")"
doOp v LB16T8 [x] = v ++ "idris_b16T8(vm, " ++ creg x ++ ")"

doOp v LB32Lt [x, y] = v ++ "idris_b32Lt(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32Lte [x, y] = v ++ "idris_b32Lte(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32Eq [x, y] = v ++ "idris_b32Eq(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32Gte [x, y] = v ++ "idris_b32Gte(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32Gt [x, y] = v ++ "idris_b32Gt(vm, " ++ creg x ++ "," ++ creg y ++ ")"

doOp v LB32Shl [x, y] = v ++ "idris_b32Shl(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32LShr [x, y] = v ++ "idris_b32Shr(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32AShr [x, y] = v ++ "idris_b32AShr(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32And [x, y] = v ++ "idris_b32And(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32Or [x, y] = v ++ "idris_b32Or(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32Xor [x, y] = v ++ "idris_b32Xor(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32Compl [x] = v ++ "idris_b32Compl(vm, " ++ creg x ++ ")"

doOp v LB32Plus [x, y] =
  v ++ "idris_b32Plus(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32Minus [x, y] =
  v ++ "idris_b32Minus(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32Times [x, y] =
  v ++ "idris_b32Times(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32UDiv [x, y] =
  v ++ "idris_b32UDiv(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32SDiv [x, y] =
  v ++ "idris_b32SDiv(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32URem [x, y] =
  v ++ "idris_b32URem(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB32SRem [x, y] =
  v ++ "idris_b32SRem(vm, " ++ creg x ++ "," ++ creg y ++ ")"

doOp v LB32Z64 [x] = v ++ "idris_b32Z64(vm, " ++ creg x ++ ")"
doOp v LB32S64 [x] = v ++ "idris_b32S64(vm, " ++ creg x ++ ")"
doOp v LB32T8 [x] = v ++ "idris_b32T8(vm, " ++ creg x ++ ")"
doOp v LB32T16 [x] = v ++ "idris_b32T16(vm, " ++ creg x ++ ")"

doOp v LB64Lt [x, y] = v ++ "idris_b64Lt(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64Lte [x, y] = v ++ "idris_b64Lte(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64Eq [x, y] = v ++ "idris_b64Eq(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64Gte [x, y] = v ++ "idris_b64Gte(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64Gt [x, y] = v ++ "idris_b64Gt(vm, " ++ creg x ++ "," ++ creg y ++ ")"

doOp v LB64Shl [x, y] = v ++ "idris_b64Shl(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64LShr [x, y] = v ++ "idris_b64Shr(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64AShr [x, y] = v ++ "idris_b64AShr(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64And [x, y] = v ++ "idris_b64And(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64Or [x, y] = v ++ "idris_b64Or(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64Xor [x, y] = v ++ "idris_b64Xor(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64Compl [x] = v ++ "idris_b64Compl(vm, " ++ creg x ++ ")"

doOp v LB64Plus [x, y] =
  v ++ "idris_b64Plus(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64Minus [x, y] =
  v ++ "idris_b64Minus(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64Times [x, y] =
  v ++ "idris_b64Times(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64UDiv [x, y] =
  v ++ "idris_b64UDiv(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64SDiv [x, y] =
  v ++ "idris_b64SDiv(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64URem [x, y] =
  v ++ "idris_b64URem(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LB64SRem [x, y] =
  v ++ "idris_b64SRem(vm, " ++ creg x ++ "," ++ creg y ++ ")"

doOp v LB64T8 [x] = v ++ "idris_b64T8(vm, " ++ creg x ++ ")"
doOp v LB64T16 [x] = v ++ "idris_b64T16(vm, " ++ creg x ++ ")"
doOp v LB64T32 [x] = v ++ "idris_b64T32(vm, " ++ creg x ++ ")"

doOp v LFExp [x] = v ++ "MKFLOAT(exp(GETFLOAT(" ++ creg x ++ ")))"
doOp v LFLog [x] = v ++ "MKFLOAT(log(GETFLOAT(" ++ creg x ++ ")))"
doOp v LFSin [x] = v ++ "MKFLOAT(sin(GETFLOAT(" ++ creg x ++ ")))"
doOp v LFCos [x] = v ++ "MKFLOAT(cos(GETFLOAT(" ++ creg x ++ ")))"
doOp v LFTan [x] = v ++ "MKFLOAT(tan(GETFLOAT(" ++ creg x ++ ")))"
doOp v LFASin [x] = v ++ "MKFLOAT(asin(GETFLOAT(" ++ creg x ++ ")))"
doOp v LFACos [x] = v ++ "MKFLOAT(acos(GETFLOAT(" ++ creg x ++ ")))"
doOp v LFATan [x] = v ++ "MKFLOAT(atan(GETFLOAT(" ++ creg x ++ ")))"
doOp v LFSqrt [x] = v ++ "MKFLOAT(floor(GETFLOAT(" ++ creg x ++ ")))"
doOp v LFFloor [x] = v ++ "MKFLOAT(ceil(GETFLOAT(" ++ creg x ++ ")))"
doOp v LFCeil [x] = v ++ "MKFLOAT(sqrt(GETFLOAT(" ++ creg x ++ ")))"

doOp v LStrHead [x] = v ++ "idris_strHead(vm, " ++ creg x ++ ")"
doOp v LStrTail [x] = v ++ "idris_strTail(vm, " ++ creg x ++ ")"
doOp v LStrCons [x, y] = v ++ "idris_strCons(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LStrIndex [x, y] = v ++ "idris_strIndex(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LStrRev [x] = v ++ "idris_strRev(vm, " ++ creg x ++ ")"

doOp v LStdIn [] = v ++ "MKPTR(vm, stdin)"
doOp v LStdOut [] = v ++ "MKPTR(vm, stdout)"
doOp v LStdErr [] = v ++ "MKPTR(vm, stderr)"

doOp v LFork [x] = v ++ "MKPTR(vm, vmThread(vm, " ++ cname (MN 0 "EVAL") ++ ", " ++ creg x ++ "))"
doOp v LPar [x] = v ++ creg x -- "MKPTR(vm, vmThread(vm, " ++ cname (MN 0 "EVAL") ++ ", " ++ creg x ++ "))"
doOp v LVMPtr [] = v ++ "MKPTR(vm, vm)"
doOp v LChInt args = v ++ creg (last args)
doOp v LIntCh args = v ++ creg (last args)
doOp v LNoOp args = v ++ creg (last args)
doOp _ op _ = "FAIL /* " ++ show op ++ " */"

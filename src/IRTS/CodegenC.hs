{-# LANGUAGE CPP #-}

module IRTS.CodegenC where

import IRTS.Bytecode
import IRTS.Lang
import IRTS.Simplified
import Core.TT
import Paths_idris

import Data.Char
import System.Process
import System.Exit
import System.IO
import System.Directory
import System.Environment
import Control.Monad

data DbgLevel = NONE | DEBUG | TRACE

codegenC :: [(Name, SDecl)] ->
            String -> -- output file name
            Bool ->   -- generate executable if True, only .o if False 
            [FilePath] -> -- include files
            String -> -- extra compiler flags
            DbgLevel ->
            IO ()
codegenC defs out exec incs libs dbg
    = do -- print defs
         let bc = map toBC defs
         let h = concatMap toDecl (map fst bc)
         let cc = concatMap (uncurry toC) bc
         d <- getDataDir
         mprog <- readFile (d ++ "/rts/idris_main.c")
         let cout = headers incs ++ debug dbg ++ h ++ cc ++ 
                     (if exec then mprog else "")
         (tmpn, tmph) <- tempfile
         hPutStr tmph cout
         hFlush tmph
         hClose tmph
         let gcc = "gcc -x c " ++ 
                     (if exec then "" else " - c ") ++
                     gccDbg dbg ++
                     " " ++ tmpn ++
                     " `idris --link` `idris --include` " ++ libs ++
                     " -lidris_rts -o " ++ out
--          putStrLn cout
         exit <- system gcc
         when (exit /= ExitSuccess) $
             putStrLn ("FAILURE: " ++ gcc)

headers [] = "#include <idris_rts.h>\n\n"
headers (x : xs) = "#include <" ++ x ++ ">\n" ++ headers xs

debug TRACE = "#define IDRIS_DEBUG\n\n"
debug _ = ""

gccDbg DEBUG = "-g"
gccDbg TRACE = "-g"
gccDbg _ = "-O2"

cname :: Name -> String
cname n = "_idris_" ++ concatMap cchar (show n)
  where cchar x | isAlpha x || isDigit x = [x]
                | otherwise = "_" ++ show (fromEnum x) ++ "_"

indent i = take (i * 4) (repeat ' ')

creg RVal = "RVAL"
creg (L i) = "LOC(" ++ show i ++ ")"
creg (T i) = "TOP(" ++ show i ++ ")"

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
    mkConst (BI i) = "MKINT(" ++ show i ++ ")" -- TODO
    mkConst (Fl f) = "MKFLOAT(vm, " ++ show f ++ ")"
    mkConst (Ch c) = "MKINT(" ++ show (fromEnum c) ++ ")"
    mkConst (Str s) = "MKSTR(vm, " ++ show s ++ ")"
    mkConst _ = "MKINT(42424242)"
bcc i (MKCON l tag args)
    = indent i ++ creg l ++ " = MKCON(vm, " ++ show tag ++ ", " ++
         show (length args) ++ concatMap showArg args ++ ");\n"
  where showArg r = ", " ++ creg r
bcc i (PROJECT l loc a) = indent i ++ "PROJECT(vm, " ++ creg l ++ ", " ++ show loc ++ 
                                      ", " ++ show a ++ ");\n"
bcc i (CASE r code def) 
    = indent i ++ "switch(TAG(" ++ creg r ++ ")) {\n" ++
      concatMap (showCase i) code ++
      showDef i def ++
      indent i ++ "}\n"
  where
    showCase i (t, bc) = indent i ++ "case " ++ show t ++ ":\n"
                         ++ concatMap (bcc (i+1)) bc ++ indent (i + 1) ++ "break;\n"
    showDef i Nothing = ""
    showDef i (Just c) = indent i ++ "default:\n" 
                         ++ concatMap (bcc (i+1)) c ++ indent (i + 1) ++ "break;\n"
bcc i (CONSTCASE r code def) 
    = indent i ++ "switch(GETINT(" ++ creg r ++ ")) {\n" ++
      concatMap (showCase i) code ++
      showDef i def ++
      indent i ++ "}\n"
  where
    showCase i (t, bc) = indent i ++ "case " ++ show t ++ ":\n"
                         ++ concatMap (bcc (i+1)) bc ++ indent (i + 1) ++ "break;\n"
    showDef i Nothing = ""
    showDef i (Just c) = indent i ++ "default:\n" 
                         ++ concatMap (bcc (i+1)) c ++ indent (i + 1) ++ "break;\n"
bcc i (CALL n) = indent i ++ "CALL(" ++ cname n ++ ");\n"
bcc i (TAILCALL n) = indent i ++ "TAILCALL(" ++ cname n ++ ");\n"
bcc i (SLIDE n) = indent i ++ "SLIDE(vm, " ++ show n ++ ");\n"
bcc i REBASE = indent i ++ "REBASE;\n"
bcc i (RESERVE n) = indent i ++ "RESERVE(" ++ show n ++ ");\n"
bcc i (ADDTOP n) = indent i ++ "ADDTOP(" ++ show n ++ ");\n"
bcc i (TOPBASE n) = indent i ++ "TOPBASE(" ++ show n ++ ");\n"
bcc i (BASETOP n) = indent i ++ "BASETOP(" ++ show n ++ ");\n"
bcc i STOREOLD = indent i ++ "STOREOLD;\n"
bcc i (OP l fn args) = indent i ++ creg l ++ " = " ++ doOp fn args ++ ";\n"
bcc i (FOREIGNCALL l LANG_C rty fn args)
      = indent i ++ creg l ++ " = " ++
        c_irts rty (fn ++ "(" ++ showSep "," (map fcall args) ++ ")") ++ ";\n"
    where fcall (t, arg) = irts_c t (creg arg)
-- bcc i _ = indent i ++ "// not done yet\n"

c_irts FInt x = "MKINT((i_int)(" ++ x ++ ")"
c_irts FString x = "MKSTR(" ++ x ++ ")"
c_irts FUnit x = "MKINT(42424242)"
c_irts FPtr x = "MKPTR(" ++ x ++ ")"
c_irts FDouble x = "MKFLOAT(vm, " ++ x ++ ")"
c_irts FAny x = x

irts_c FInt x = "GETINT(" ++ x ++ ")"
irts_c FString x = "GETSTR(" ++ x ++ ")"
irts_c FUnit x = x
irts_c FPtr x = "GETPTR(" ++ x ++ ")"
irts_c FDouble x = "GETFLOAT(" ++ x ++ ")"
irts_c FAny x = x

doOp LPlus [l, r] = "ADD(" ++ creg l ++ ", " ++ creg r ++ ")"
doOp LMinus [l, r] = "INTOP(-," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LTimes [l, r] = "MULT(" ++ creg l ++ ", " ++ creg r ++ ")"
doOp LDiv [l, r] = "INTOP(/," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LEq [l, r] = "INTOP(==," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LLt [l, r] = "INTOP(<," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LLe [l, r] = "INTOP(<=," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LGt [l, r] = "INTOP(>," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LGe [l, r] = "INTOP(>=," ++ creg l ++ ", " ++ creg r ++ ")"

doOp LFPlus [l, r] = "FLOATOP(+" ++ creg l ++ ", " ++ creg r ++ ")"
doOp LFMinus [l, r] = "FLOATOP(-," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LFTimes [l, r] = "FLOATOP(*" ++ creg l ++ ", " ++ creg r ++ ")"
doOp LFDiv [l, r] = "FLOATOP(/," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LFEq [l, r] = "FLOATBOP(==," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LFLt [l, r] = "FLOATBOP(<," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LFLe [l, r] = "FLOATBOP(<=," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LFGt [l, r] = "FLOATBOP(>," ++ creg l ++ ", " ++ creg r ++ ")"
doOp LFGe [l, r] = "FLOATBOP(>=," ++ creg l ++ ", " ++ creg r ++ ")"

doOp LStrConcat [l,r] = "idris_concat(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp LStrLt [l,r] = "idris_strlt(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp LStrEq [l,r] = "idris_streq(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp LStrLen [x] = "idris_strlen(vm, " ++ creg x ++ ")"

doOp LIntFloat [x] = "idris_castIntFloat(" ++ creg x ++ ")"
doOp LFloatInt [x] = "idris_castFloatInt(" ++ creg x ++ ")"
doOp LIntStr [x] = "idris_castIntStr(vm, " ++ creg x ++ ")"
doOp LStrInt [x] = "idris_castFloatStr(vm, " ++ creg x ++ ")"
doOp LFloatStr [x] = "idris_castFloatStr(vm, " ++ creg x ++ ")"
doOp LStrFloat [x] = "idris_castStrFloat(vm, " ++ creg x ++ ")"

doOp LReadStr [] = "idris_readStr(vm, stdin)"
doOp LPrintNum [x] = "NULL; printf(\"%ld\\n\", GETINT(" ++ creg x ++ "))"
doOp LPrintStr [x] = "NULL; puts(GETSTR(" ++ creg x ++ "))"
doOp _ _ = "FAIL"

tempfile :: IO (FilePath, Handle)
tempfile = do env <- environment "TMPDIR"
              let dir = case env of
                              Nothing -> "/tmp"
                              (Just d) -> d
              openTempFile dir "idris"

environment :: String -> IO (Maybe String)
environment x = catch (do e <- getEnv x
                          return (Just e))
#if MIN_VERSION_base(4,6,0)
                          (\y-> do return (y::SomeException);  return Nothing)  
#endif
#if !MIN_VERSION_base(4,6,0)
                          (\_->  return Nothing)  
#endif  

{-|
Module      : IRTS.CodegenC
Description : The default code generator for Idris, generating C code.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module IRTS.CodegenC (codegenC) where

import Idris.AbsSyntax
import Idris.Core.TT
import IRTS.Bytecode
import IRTS.CodegenCommon
import IRTS.Defunctionalise
import IRTS.Lang
import IRTS.Simplified
import IRTS.System

import Util.System

import Control.Monad
import Data.Bits
import Data.Char
import Data.List (intercalate, nubBy)
import Debug.Trace
import Numeric
import System.Directory
import System.Exit
import System.FilePath ((<.>), (</>))
import System.IO
import System.Process

codegenC :: CodeGenerator
codegenC ci = do codegenC' (simpleDecls ci)
                           (outputFile ci)
                           (outputType ci)
                           (includes ci)
                           (compileObjs ci)
                           (map mkLib (compileLibs ci) ++
                               map incdir (importDirs ci))
                           (compilerFlags ci)
                           (exportDecls ci)
                           (interfaces ci)
                           (debugLevel ci)
                 when (interfaces ci) $
                   codegenH (exportDecls ci)

  where mkLib l = "-l" ++ l
        incdir i = "-I" ++ i

codegenC' :: [(Name, SDecl)]
          -> String        -- ^ output file name
          -> OutputType    -- ^ generate executable if True, only .o if False
          -> [FilePath]    -- ^ include files
          -> [String]      -- ^ extra object files
          -> [String]      -- ^ extra compiler flags (libraries)
          -> [String]      -- ^ extra compiler flags (anything)
          -> [ExportIFace]
          -> Bool          -- ^ interfaces too (so make a .o instead)
          -> DbgLevel
          -> IO ()
codegenC' defs out exec incs objs libs flags exports iface dbg
    = do -- print defs
         let bc = map toBC defs
         let wrappers = genWrappers bc
         let h = concatMap toDecl (map fst bc)
         let cc = concatMap (uncurry toC) bc
         let hi = concatMap ifaceC (concatMap getExp exports)
         d <- getIdrisCRTSDir
         mprog <- readFile (d </> "idris_main" <.> "c")
         let cout = headers incs ++ debug dbg ++ h ++ wrappers ++ cc ++
                     (if (exec == Executable) then mprog else hi)
         case exec of
           Raw -> writeSource out cout
           _ -> do
             (tmpn, tmph) <- tempfile ".c"
             hPutStr tmph cout
             hFlush tmph
             hClose tmph
             comp <- getCC
             libFlags <- getLibFlags
             incFlags <- getIncFlags
             envFlags <- getEnvFlags
             let stackFlag = if isWindows then ["-Wl,--stack,16777216"] else []
             let args = [gccDbg dbg] ++
                        gccFlags iface ++
                        -- # Any flags defined here which alter the RTS API must also be added to config.mk
                        ["-DHAS_PTHREAD", "-DIDRIS_ENABLE_STATS",
                         "-I."] ++ objs ++ envFlags ++
                        (if (exec == Executable) then [] else ["-c"]) ++
                        [tmpn] ++
                        (if not iface then libFlags else []) ++
                        incFlags ++
                        (if not iface then libs else []) ++
                        flags ++ stackFlag ++
                        ["-o", out]
--              putStrLn (show args)
             exit <- rawSystem comp args
             when (exit /= ExitSuccess) $
                putStrLn ("FAILURE: " ++ show comp ++ " " ++ show args)
  where
    getExp (Export _ _ exp) = exp

headers xs =
  concatMap
    (\h -> "#include \"" ++ h ++ "\"\n")
    (xs ++ ["idris_rts.h", "idris_bitstring.h", "idris_stdfgn.h"])

debug TRACE = "#define IDRIS_TRACE\n\n"
debug _ = ""

-- We're using signed integers now. Make sure we get consistent semantics
-- out of them from gcc. See e.g. http://thiemonagel.de/2010/01/signed-integer-overflow/
gccFlags i = if i then ["-fwrapv"]
                  else ["-fwrapv", "-fno-strict-overflow"]

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
        | otherwise = showHexes (utf8bytes (ord c))

    utf8bytes :: Int -> [Int]
    utf8bytes x = let (h : bytes) = split [] x in
                      headHex h (length bytes) : map toHex bytes
      where
        split acc 0 = acc
        split acc x = let xbits = x .&. 0x3f
                          xrest = shiftR x 6 in
                          split (xbits : acc) xrest

        headHex h 1 = h + 0xc0
        headHex h 2 = h + 0xe0
        headHex h 3 = h + 0xf0
        headHex h n = error "Can't happen: Invalid UTF8 character"

        toHex i = i + 0x80

    showHexes = foldr ((++) . showUTF8) ""
    showUTF8 c = "\"\"\\x" ++ showHex c "\"\""

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
    mkConst (B8  x) = "idris_b8const(vm, "  ++ show x ++ "U)"
    mkConst (B16 x) = "idris_b16const(vm, " ++ show x ++ "U)"
    mkConst (B32 x) = "idris_b32const(vm, " ++ show x ++ "UL)"
    mkConst (B64 x) = "idris_b64const(vm, " ++ show x ++ "ULL)"
    -- if it's a type constant, we won't use it, but equally it shouldn't
    -- report an error. These might creep into generated for various reasons
    -- (especially if erasure is disabled).
    mkConst c | isTypeConst c = "MKINT(42424242)"
    mkConst c = error $ "mkConst of (" ++ show c ++ ") not implemented"

bcc i (UPDATE l r) = indent i ++ creg l ++ " = " ++ creg r ++ ";\n"
bcc i (MKCON l loc tag []) | tag < 256
    = indent i ++ creg l ++ " = NULL_CON(" ++ show tag ++ ");\n"
bcc i (MKCON l loc tag args)
    = indent i ++ alloc loc tag ++
      indent i ++ setArgs 0 args ++ "\n" ++
      indent i ++ creg l ++ " = " ++ creg Tmp ++ ";\n"

--         "MKCON(vm, " ++ creg l ++ ", " ++ show tag ++ ", " ++
--         show (length args) ++ concatMap showArg args ++ ");\n"
  where showArg r = ", " ++ creg r
        setArgs i [] = ""
        setArgs i (x : xs) = "SETARG(" ++ creg Tmp ++ ", " ++ show i ++ ", " ++ creg x ++
                             "); " ++ setArgs (i + 1) xs
        alloc Nothing tag
            = "allocCon(" ++ creg Tmp ++ ", vm, " ++ show tag ++ ", " ++
                    show (length args) ++ ", 0);\n"
        alloc (Just old) tag
            = "updateCon(" ++ creg Tmp ++ ", " ++ creg old ++ ", " ++ show tag ++ ", " ++
                    show (length args) ++ ");\n"

bcc i (PROJECT l loc a) = indent i ++ "PROJECT(vm, " ++ creg l ++ ", " ++ show loc ++
                                      ", " ++ show a ++ ");\n"
bcc i (PROJECTINTO r t idx)
    = indent i ++ creg r ++ " = GETARG(" ++ creg t ++ ", " ++ show idx ++ ");\n"
bcc i (CASE True r code def)
    | length code < 4 = showCase i def code
  where
    showCode :: Int -> [BC] -> String
    showCode i bc = "{\n" ++ concatMap (bcc (i + 1)) bc ++
                    indent i ++ "}\n"

    showCase :: Int -> Maybe [BC] -> [(Int, [BC])] -> String
    showCase i Nothing [(t, c)] = indent i ++ showCode i c
    showCase i (Just def) [] = indent i ++ showCode i def
    showCase i def ((t, c) : cs)
        = indent i ++ "if (CTAG(" ++ creg r ++ ") == " ++ show t ++ ") " ++ showCode i c
           ++ indent i ++ "else\n" ++ showCase i def cs

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
    intConsts ((B8 _, _ ) : _) = True
    intConsts ((B16 _, _ ) : _) = True
    intConsts ((B32 _, _ ) : _) = True
    intConsts ((B64 _, _ ) : _) = True
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
    iCase v (B8 w, bc) =
        indent i ++ "if (GETBITS8(" ++ v ++ ") == " ++ show (fromEnum w) ++ ") {\n"
           ++ concatMap (bcc (i+1)) bc ++ indent i ++ "} else\n"
    iCase v (B16 w, bc) =
        indent i ++ "if (GETBITS16(" ++ v ++ ") == " ++ show (fromEnum w) ++ ") {\n"
           ++ concatMap (bcc (i+1)) bc ++ indent i ++ "} else\n"
    iCase v (B32 w, bc) =
        indent i ++ "if (GETBITS32(" ++ v ++ ") == " ++ show (fromEnum w) ++ ") {\n"
           ++ concatMap (bcc (i+1)) bc ++ indent i ++ "} else\n"
    iCase v (B64 w, bc) =
        indent i ++ "if (GETBITS64(" ++ v ++ ") == " ++ show (fromEnum w) ++ ") {\n"
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
bcc i (FOREIGNCALL l rty (FStr fn@('&':name)) [])
      = indent i ++
        c_irts (toFType rty) (creg l ++ " = ") fn ++ ";\n"
bcc i (FOREIGNCALL l rty (FStr fn) (x:xs)) | fn == "%wrapper"
      = indent i ++
        c_irts (toFType rty) (creg l ++ " = ")
            ("_idris_get_wrapper(" ++ creg (snd x) ++ ")") ++ ";\n"
bcc i (FOREIGNCALL l rty (FStr fn) (x:xs)) | fn == "%dynamic"
      = indent i ++ c_irts (toFType rty) (creg l ++ " = ")
            ("(*(" ++ cFnSig "" rty xs ++ ") GETPTR(" ++ creg (snd x) ++ "))" ++
             "(" ++ showSep "," (map fcall xs) ++ ")") ++ ";\n"
bcc i (FOREIGNCALL l rty (FStr fn) args)
      = indent i ++
        c_irts (toFType rty) (creg l ++ " = ")
                   (fn ++ "(" ++ showSep "," (map fcall args) ++ ")") ++ ";\n"
bcc i (FOREIGNCALL l rty _ args) = error "Foreign Function calls cannot be partially applied, without being inlined."
bcc i (NULL r) = indent i ++ creg r ++ " = NULL;\n" -- clear, so it'll be GCed
bcc i (ERROR str) = indent i ++ "fprintf(stderr, " ++ show str ++ "); fprintf(stderr, \"\\n\"); exit(-1);\n"
-- bcc i c = error (show c) -- indent i ++ "// not done yet\n"

fcall (t, arg) = irts_c (toFType t) (creg arg)
-- Deconstruct the Foreign type in the defunctionalised expression and build
-- a foreign type description for c_irts and irts_c
toAType (FCon i)
    | i == sUN "C_IntChar" = ATInt ITChar
    | i == sUN "C_IntNative" = ATInt ITNative
    | i == sUN "C_IntBits8" = ATInt (ITFixed IT8)
    | i == sUN "C_IntBits16" = ATInt (ITFixed IT16)
    | i == sUN "C_IntBits32" = ATInt (ITFixed IT32)
    | i == sUN "C_IntBits64" = ATInt (ITFixed IT64)
toAType t = error (show t ++ " not defined in toAType")

toFType (FCon c)
    | c == sUN "C_Str" = FString
    | c == sUN "C_Float" = FArith ATFloat
    | c == sUN "C_Ptr" = FPtr
    | c == sUN "C_MPtr" = FManagedPtr
    | c == sUN "C_CData" = FCData
    | c == sUN "C_Unit" = FUnit
toFType (FApp c [_,ity])
    | c == sUN "C_IntT" = FArith (toAType ity)
    | c == sUN "C_FnT" = toFunType ity
toFType (FApp c [_])
    | c == sUN "C_Any" = FAny
toFType t = FAny

toFunType (FApp c [_,ity])
    | c == sUN "C_FnBase" = FFunction
    | c == sUN "C_FnIO" = FFunctionIO
toFunType (FApp c [_,_,_,ity])
    | c == sUN "C_Fn" = toFunType ity
toFunType _ = FAny

c_irts (FArith (ATInt ITNative)) l x = l ++ "MKINT((i_int)(" ++ x ++ "))"
c_irts (FArith (ATInt ITChar))  l x = c_irts (FArith (ATInt ITNative)) l x
c_irts (FArith (ATInt (ITFixed ity))) l x
    = l ++ "idris_b" ++ show (nativeTyWidth ity) ++ "const(vm, " ++ x ++ ")"
c_irts FString l x = l ++ "MKSTR(vm, " ++ x ++ ")"
c_irts FUnit l x = x
c_irts FPtr l x = l ++ "MKPTR(vm, " ++ x ++ ")"
c_irts FManagedPtr l x = l ++ "MKMPTR(vm, " ++ x ++ ")"
c_irts (FArith ATFloat) l x = l ++ "MKFLOAT(vm, " ++ x ++ ")"
c_irts FCData l x = l ++ "MKCDATA(vm, " ++ x ++ ")"
c_irts FAny l x = l ++ x
c_irts FFunction l x = error "Return of function from foreign call is not supported"
c_irts FFunctionIO l x = error "Return of function from foreign call is not supported"

irts_c (FArith (ATInt ITNative)) x = "GETINT(" ++ x ++ ")"
irts_c (FArith (ATInt ITChar)) x = irts_c (FArith (ATInt ITNative)) x
irts_c (FArith (ATInt (ITFixed ity))) x
    = "(" ++ x ++ "->info.bits" ++ show (nativeTyWidth ity) ++ ")"
irts_c FString x = "GETSTR(" ++ x ++ ")"
irts_c FUnit x = x
irts_c FPtr x = "GETPTR(" ++ x ++ ")"
irts_c FManagedPtr x = "GETMPTR(" ++ x ++ ")"
irts_c (FArith ATFloat) x = "GETFLOAT(" ++ x ++ ")"
irts_c FCData x = "GETCDATA(" ++ x ++ ")"
irts_c FAny x = x
irts_c FFunctionIO x = wrapped x
irts_c FFunction x = wrapped x

cFnSig name rty [] = ctype rty ++ " (*" ++ name ++ ")(void) "
cFnSig name rty args = ctype rty ++ " (*" ++ name ++ ")("
        ++ showSep "," (map (ctype . fst) args) ++ ") "

wrapped x = "_idris_get_wrapper(" ++ x ++ ")"

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
doOp v (LAnd ITBig) [l, r] = v ++ "idris_bigAnd(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LOr ITBig) [l, r] = v ++ "idris_bigOr(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSHL ITBig) [l, r] = v ++ "idris_bigShiftLeft(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LLSHR ITBig) [l, r] = v ++ "idris_bigLShiftRight(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LASHR ITBig) [l, r] = v ++ "idris_bigAShiftRight(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LEq (ATInt ITBig)) [l, r] = v ++ "idris_bigEq(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSLt (ATInt ITBig)) [l, r] = v ++ "idris_bigLt(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSLe (ATInt ITBig)) [l, r] = v ++ "idris_bigLe(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSGt (ATInt ITBig)) [l, r] = v ++ "idris_bigGt(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v (LSGe (ATInt ITBig)) [l, r] = v ++ "idris_bigGe(vm, " ++ creg l ++ ", " ++ creg r ++ ")"

doOp v (LIntFloat ITNative) [x] = v ++ "idris_castIntFloat(" ++ creg x ++ ")"
doOp v (LFloatInt ITNative) [x] = v ++ "idris_castFloatInt(" ++ creg x ++ ")"
doOp v (LSExt ITNative ITBig) [x] = v ++ "idris_castIntBig(vm, " ++ creg x ++ ")"
doOp v (LTrunc ITBig ITNative) [x] = v ++ "idris_castBigInt(vm, " ++ creg x ++ ")"
doOp v (LStrInt ITBig) [x] = v ++ "idris_castStrBig(vm, " ++ creg x ++ ")"
doOp v (LIntStr ITBig) [x] = v ++ "idris_castBigStr(vm, " ++ creg x ++ ")"
doOp v (LIntStr ITNative) [x] = v ++ "idris_castIntStr(vm, " ++ creg x ++ ")"
doOp v (LStrInt ITNative) [x] = v ++ "idris_castStrInt(vm, " ++ creg x ++ ")"
doOp v (LIntStr (ITFixed _)) [x] = v ++ "idris_castBitsStr(vm, " ++ creg x ++ ")"
doOp v LFloatStr [x] = v ++ "idris_castFloatStr(vm, " ++ creg x ++ ")"
doOp v LStrFloat [x] = v ++ "idris_castStrFloat(vm, " ++ creg x ++ ")"

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
    = v ++ "idris_b" ++ show (nativeTyWidth to) ++ "const(vm, (uintptr_t)GETINT(" ++ creg x ++ "))"
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
doOp v (LTrunc ITBig (ITFixed IT64)) [x]
    = v ++ "idris_b64const(vm, ISINT(" ++ creg x ++ ") ? GETINT(" ++ creg x ++ ") : idris_truncBigB64(GETMPZ(" ++ creg x ++ ")))"
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
doOp v LFNegate [x] = v ++ "MKFLOAT(vm, -GETFLOAT(" ++ (creg x) ++ "))"

-- String functions which don't need to know we're UTF8
doOp v LStrConcat [l,r] = v ++ "idris_concat(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LStrLt [l,r] = v ++ "idris_strlt(vm, " ++ creg l ++ ", " ++ creg r ++ ")"
doOp v LStrEq [l,r] = v ++ "idris_streq(vm, " ++ creg l ++ ", " ++ creg r ++ ")"

doOp v LReadStr [_] = v ++ "idris_readStr(vm, stdin)"
doOp v LWriteStr [_,s]
             = v ++ "MKINT((i_int)(idris_writeStr(stdout"
                 ++ ",GETSTR("
                 ++ creg s ++ "))))"


-- String functions which need to know we're UTF8
doOp v LStrHead [x] = v ++ "idris_strHead(vm, " ++ creg x ++ ")"
doOp v LStrTail [x] = v ++ "idris_strTail(vm, " ++ creg x ++ ")"
doOp v LStrCons [x, y] = v ++ "idris_strCons(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LStrIndex [x, y] = v ++ "idris_strIndex(vm, " ++ creg x ++ "," ++ creg y ++ ")"
doOp v LStrRev [x] = v ++ "idris_strRev(vm, " ++ creg x ++ ")"
doOp v LStrLen [x] = v ++ "idris_strlen(vm, " ++ creg x ++ ")"
doOp v LStrSubstr [x,y,z] = v ++ "idris_substr(vm, " ++ creg x ++ "," ++ creg y ++ "," ++ creg z ++ ")"

doOp v LFork [x] = v ++ "MKPTR(vm, vmThread(vm, " ++ cname (sMN 0 "EVAL") ++ ", " ++ creg x ++ "))"
doOp v LPar [x] = v ++ creg x -- "MKPTR(vm, vmThread(vm, " ++ cname (MN 0 "EVAL") ++ ", " ++ creg x ++ "))"
doOp v (LChInt ITNative) args = v ++ creg (last args)
doOp v (LChInt ITChar) args = doOp v (LChInt ITNative) args
doOp v (LIntCh ITNative) args = v ++ creg (last args)
doOp v (LIntCh ITChar) args = doOp v (LIntCh ITNative) args

doOp v LSystemInfo [x] = v ++ "idris_systemInfo(vm, " ++ creg x ++ ")"
doOp v LCrash [x] = "idris_crash(GETSTR(" ++ creg x ++ "))"
doOp v LNoOp args = v ++ creg (last args)

-- Pointer primitives (declared as %extern in Builtins.idr)
doOp v (LExternal rf) [_,x]
   | rf == sUN "prim__readFile"
       = v ++ "idris_readStr(vm, GETPTR(" ++ creg x ++ "))"
doOp v (LExternal rf) [_,len,x]
   | rf == sUN "prim__readChars"
       = v ++ "idris_readChars(vm, GETINT(" ++ creg len ++
                                "), GETPTR(" ++ creg x ++ "))"
doOp v (LExternal wf) [_,x,s]
   | wf == sUN "prim__writeFile"
       = v ++ "MKINT((i_int)(idris_writeStr(GETPTR(" ++ creg x
                              ++ "),GETSTR("
                              ++ creg s ++ "))))"
doOp v (LExternal si) [] | si == sUN "prim__stdin" = v ++ "MKPTR(vm, stdin)"
doOp v (LExternal so) [] | so == sUN "prim__stdout" = v ++ "MKPTR(vm, stdout)"
doOp v (LExternal se) [] | se == sUN "prim__stderr" = v ++ "MKPTR(vm, stderr)"

doOp v (LExternal vm) [_] | vm == sUN "prim__vm" = v ++ "MKPTR(vm, vm)"
doOp v (LExternal nul) [] | nul == sUN "prim__null" = v ++ "MKPTR(vm, NULL)"
doOp v (LExternal eqp) [x, y] | eqp == sUN "prim__eqPtr"
    = v ++ "MKINT((i_int)(GETPTR(" ++ creg x ++ ") == GETPTR(" ++ creg y ++ ")))"
doOp v (LExternal eqp) [x, y] | eqp == sUN "prim__eqManagedPtr"
    = v ++ "MKINT((i_int)(GETMPTR(" ++ creg x ++ ") == GETMPTR(" ++ creg y ++ ")))"
doOp v (LExternal rp) [p, i] | rp == sUN "prim__registerPtr"
    = v ++ "MKMPTR(vm, GETPTR(" ++ creg p ++ "), GETINT(" ++ creg i ++ "))"
doOp v (LExternal pk) [_, p, o] | pk == sUN "prim__peek8"
    = v ++ "idris_peekB8(vm," ++ creg p ++ "," ++ creg o ++")"
doOp v (LExternal pk) [_, p, o, x] | pk == sUN "prim__poke8"
    = v ++ "idris_pokeB8(" ++ creg p ++ "," ++ creg o ++ "," ++ creg x ++ ")"
doOp v (LExternal pk) [_, p, o] | pk == sUN "prim__peek16"
    = v ++ "idris_peekB16(vm," ++ creg p ++ "," ++ creg o ++")"
doOp v (LExternal pk) [_, p, o, x] | pk == sUN "prim__poke16"
    = v ++ "idris_pokeB16(" ++ creg p ++ "," ++ creg o ++ "," ++ creg x ++ ")"
doOp v (LExternal pk) [_, p, o] | pk == sUN "prim__peek32"
    = v ++ "idris_peekB32(vm," ++ creg p ++ "," ++ creg o ++")"
doOp v (LExternal pk) [_, p, o, x] | pk == sUN "prim__poke32"
    = v ++ "idris_pokeB32(" ++ creg p ++ "," ++ creg o ++ "," ++ creg x ++ ")"
doOp v (LExternal pk) [_, p, o] | pk == sUN "prim__peek64"
    = v ++ "idris_peekB64(vm," ++ creg p ++ "," ++ creg o ++")"
doOp v (LExternal pk) [_, p, o, x] | pk == sUN "prim__poke64"
    = v ++ "idris_pokeB64(" ++ creg p ++ "," ++ creg o ++ "," ++ creg x ++ ")"
doOp v (LExternal pk) [_, p, o] | pk == sUN "prim__peekPtr"
    = v ++ "idris_peekPtr(vm," ++ creg p ++ "," ++ creg o ++")"
doOp v (LExternal pk) [_, p, o, x] | pk == sUN "prim__pokePtr"
    = v ++ "idris_pokePtr(" ++ creg p ++ "," ++ creg o ++ "," ++ creg x ++ ")"
doOp v (LExternal pk) [_, p, o, x] | pk == sUN "prim__pokeDouble"
    = v ++ "idris_pokeDouble(" ++ creg p ++ "," ++ creg o ++ "," ++ creg x ++ ")"
doOp v (LExternal pk) [_, p, o] | pk == sUN "prim__peekDouble"
    = v ++ "idris_peekDouble(vm," ++ creg p ++ "," ++ creg o ++")"
doOp v (LExternal pk) [_, p, o, x] | pk == sUN "prim__pokeSingle"
    = v ++ "idris_pokeSingle(" ++ creg p ++ "," ++ creg o ++ "," ++ creg x ++ ")"
doOp v (LExternal pk) [_, p, o] | pk == sUN "prim__peekSingle"
    = v ++ "idris_peekSingle(vm," ++ creg p ++ "," ++ creg o ++")"
doOp v (LExternal pk) [] | pk == sUN "prim__sizeofPtr"
    = v ++ "MKINT(sizeof(void*))"
doOp v (LExternal mpt) [p] | mpt == sUN "prim__asPtr"
    = v ++ "MKPTR(vm, GETMPTR("++ creg p ++"))"
doOp v (LExternal offs) [p, n] | offs == sUN "prim__ptrOffset"
    = v ++ "MKPTR(vm, (void *)((char *)GETPTR(" ++ creg p ++ ") + GETINT(" ++ creg n ++ ")))"
doOp _ op args = error $ "doOp not implemented (" ++ show (op, args) ++ ")"


flUnOp :: String -> String -> String
flUnOp name val = "MKFLOAT(vm, " ++ name ++ "(GETFLOAT(" ++ val ++ ")))"

-------------------- Interface file generation

-- First, the wrappers in the C file

ifaceC :: Export -> String
ifaceC (ExportData n) = "typedef VAL " ++ cdesc n ++ ";\n"
ifaceC (ExportFun n cn ret args)
   = ctype ret ++ " " ++ cdesc cn ++
         "(VM* vm" ++ showArgs (zip argNames args) ++ ") {\n"
       ++ mkBody n (zip argNames args) ret ++ "}\n\n"
  where showArgs [] = ""
        showArgs ((n, t) : ts) = ", " ++ ctype t ++ " " ++ n ++
                                 showArgs ts

        argNames = zipWith (++) (repeat "arg") (map show [0..])

mkBody n as t = indent 1 ++ "INITFRAME;\n" ++
                indent 1 ++ "RESERVE(" ++ show (max (length as) 3) ++ ");\n" ++
                push 0 as ++ call n ++ retval t
  where push i [] = ""
        push i ((n, t) : ts) = indent 1 ++ c_irts (toFType t)
                                      ("TOP(" ++ show i ++ ") = ") n
                                   ++ ";\n" ++ push (i + 1) ts

        call _ = indent 1 ++ "STOREOLD;\n" ++
                 indent 1 ++ "BASETOP(0);\n" ++
                 indent 1 ++ "ADDTOP(" ++ show (length as) ++ ");\n" ++
                 indent 1 ++ "CALL(" ++ cname n ++ ");\n"

        retval (FIO t)
           = indent 1 ++ "TOP(0) = NULL;\n" ++
             indent 1 ++ "TOP(1) = NULL;\n" ++
             indent 1 ++ "TOP(2) = RVAL;\n" ++
             indent 1 ++ "STOREOLD;\n" ++
             indent 1 ++ "BASETOP(0);\n" ++
             indent 1 ++ "ADDTOP(3);\n" ++
             indent 1 ++ "CALL(" ++ cname (sUN "call__IO") ++ ");\n" ++
             retval t
        retval t = indent 1 ++ "return " ++ irts_c (toFType t) "RVAL" ++ ";\n"

ctype (FCon c)
  | c == sUN "C_Str" = "char*"
  | c == sUN "C_Float" = "float"
  | c == sUN "C_Ptr" = "void*"
  | c == sUN "C_MPtr" = "void*"
  | c == sUN "C_Unit" = "void"
ctype (FApp c [_,ity])
  | c == sUN "C_IntT" = carith ity
ctype (FApp c [_])
  | c == sUN "C_Any" = "VAL"
ctype (FStr s) = s
ctype FUnknown = "void*"
ctype (FIO t) = ctype t
ctype t = error "Can't happen: Not a valid interface type " ++ show t

carith (FCon i)
  | i == sUN "C_IntChar" = "char"
  | i == sUN "C_IntNative" = "int"
  | i == sUN "C_IntBits8" = "uint8_t"
  | i == sUN "C_IntBits16" = "uint16_t"
  | i == sUN "C_IntBits32" = "uint32_t"
  | i == sUN "C_IntBits64" = "uint64_t"
carith t = error $ "Can't happen: Not an exportable arithmetic type " ++ show t

cdesc (FStr s) = s
cdesc s = error "Can't happen: Not a valid C name"

-- Then, the header files

codegenH :: [ExportIFace] -> IO ()
codegenH es = mapM_ writeIFace es

writeIFace :: ExportIFace -> IO ()
writeIFace (Export ffic hdr exps)
   | ffic == sNS (sUN "FFI_C") ["FFI_C"]
       = do let hfile = "#ifndef " ++ hdr_guard hdr ++ "\n" ++
                        "#define " ++ hdr_guard hdr ++ "\n\n" ++
                        "#include <idris_rts.h>\n\n" ++
                        concatMap hdr_export exps ++ "\n" ++
                        "#endif\n\n"
            writeFile hdr hfile
   | otherwise = return ()

hdr_guard x = "__" ++ map hchar x
  where hchar x | isAlphaNum x = toUpper x
        hchar _ = '_'

hdr_export :: Export -> String
hdr_export (ExportData n) = "typedef VAL " ++ cdesc n ++ ";\n"
hdr_export (ExportFun n cn ret args)
   = ctype ret ++ " " ++ cdesc cn ++
         "(VM* vm" ++ showArgs (zip argNames args) ++ ");\n"
  where showArgs [] = ""
        showArgs ((n, t) : ts) = ", " ++ ctype t ++ " " ++ n ++
                                 showArgs ts

        argNames = zipWith (++) (repeat "arg") (map show [0..])

------------------ Callback wrapper generation ----------------
-- Generate callback wrappers and a function to select the
-- correct wrapper function to pass.
-- TODO: This is limited to functions that are specified in
-- the foreign call. Otherwise we would have to generate wrappers for all
-- functions with correct arity or do flow analysis
-- to find all possible inputs to the foreign call.
genWrappers :: [(Name, [BC])] -> String
genWrappers bcs = let
                    tags = nubBy (\x y -> snd x == snd y)  $ concatMap (getCallback . snd) bcs
                  in
                    case tags of
                        [] -> ""
                        t -> concatMap genWrapper t ++ genDispatcher t

genDispatcher :: [(FDesc, Int)] -> String
genDispatcher tags = "void* _idris_get_wrapper(VAL con)\n" ++
                     "{\n" ++
                     indent 1 ++ "switch(TAG(con)) {\n" ++
                     concatMap makeSwitch tags ++
                     indent 1 ++ "}\n" ++
                     indent 1 ++ "fprintf(stderr, \"No wrapper for callback\");\n" ++
                     indent 1 ++ "exit(-1);\n" ++
                     "}\n\n"
                        where
                            makeSwitch (_, tag) =
                                    indent 1 ++ "case " ++ show tag ++ ":\n" ++
                                    indent 2 ++ "return (void*) &" ++ wrapperName tag ++ ";\n"

genWrapper :: (FDesc, Int) -> String
genWrapper (desc, tag) | (toFType desc) == FFunctionIO =
    error "Cannot create C callbacks for IO functions, wrap them with unsafePerformIO.\n"
genWrapper (desc, tag) =  ret ++ " " ++ wrapperName tag ++ "(" ++
                          renderArgs argList ++")\n"  ++
                          "{\n" ++
                          (if ret /= "void" then indent 1 ++ ret ++ " ret;\n" else "") ++
                          indent 1 ++ "VM* vm = get_vm();\n" ++
                          indent 1 ++ "if (vm == NULL) {\n" ++
                          indent 2 ++ "vm = idris_vm();\n" ++
                          indent 1 ++ "}\n" ++
                          indent 1 ++ "INITFRAME;\n" ++
                          indent 1 ++ "RESERVE(" ++ show (len + 1) ++ ");\n" ++
                          indent 1 ++ "allocCon(REG1, vm, " ++ show tag ++ ",0 , 0);\n" ++
                          indent 1 ++ "TOP(0) = REG1;\n" ++
                          applyArgs argList ++
                          if ret /= "void"
                            then indent 1 ++ "ret = " ++ irts_c (toFType ft) "RVAL" ++ ";\n"
                                          ++ indent 1 ++ "return ret;\n}\n\n"
                            else "}\n\n"
                    where
                        (ret, ft) = rty desc
                        argList = zip (args desc) [0..]
                        len = length argList

                        applyArgs (x:y:xs) = push 1 [x] ++
                                            indent 1 ++ "STOREOLD;\n" ++
                                            indent 1 ++ "BASETOP(0);\n" ++
                                            indent 1 ++ "ADDTOP(2);\n" ++
                                            indent 1 ++ "CALL(_idris__123_APPLY_95_0_125_);\n" ++
                                            indent 1 ++ "TOP(0)=REG1;\n" ++
                                            applyArgs (y:xs)
                        applyArgs x = push 1 x ++
                                      indent 1 ++ "STOREOLD;\n" ++
                                      indent 1 ++ "BASETOP(0);\n" ++
                                      indent 1 ++ "ADDTOP(" ++ show (length x + 1) ++ ");\n" ++
                                      indent 1 ++ "CALL(_idris__123_APPLY_95_0_125_);\n"
                        renderArgs [] = "void"
                        renderArgs [((s, _), n)] = s ++ " a" ++ (show n)
                        renderArgs (((s, _), n):xs) = s ++ " a" ++ (show n) ++ ", " ++
                                    renderArgs xs
                        rty (FApp c [_,ty])
                            | c == sUN "C_FnBase" = (ctype ty, ty)
                            | c == sUN "C_FnIO" = (ctype ty, ty)
                            | c == sUN "C_FnT" = rty ty
                        rty (FApp c [_,_,ty,fn])
                            | c == sUN "C_Fn" = rty fn
                        rty x = ("", x)
                        args (FApp c [_,ty])
                            | c == sUN "C_FnBase" = []
                            | c == sUN "C_FnIO" = []
                            | c == sUN "C_FnT" = args ty
                        args (FApp c [_,_,ty,fn])
                            | toFType ty == FUnit = []
                            | c == sUN "C_Fn" = (ctype ty, ty) : args fn
                        args _ = []
                        push i [] = ""
                        push i (((c, t), n) : ts) = indent 1 ++ c_irts (toFType t)
                                      ("TOP(" ++ show i ++ ") = ") ("a" ++ show n)
                                   ++ ";\n" ++ push (i + 1) ts

wrapperName :: Int -> String
wrapperName tag = "_idris_wrapper_" ++ show tag

getCallback :: [BC] -> [(FDesc, Int)]
getCallback bc = getCallback' (reverse bc)
    where
        getCallback' (x:xs) = case hasCallback x of
                                [] -> getCallback' xs
                                cbs -> case findCons cbs xs of
                                        [] -> error "Idris function couldn't be wrapped."
                                        x -> x
        getCallback' [] = []
        findCons (c:cs) xs = findCon c xs ++ findCons cs xs
        findCons [] _ = []
        findCon c ((MKCON l loc tag args):xs) | snd c == l = [(fst c, tag)]
        findCon c (_:xs) = findCon c xs
        findCon c [] = []

hasCallback :: BC -> [(FDesc, Reg)]
hasCallback (FOREIGNCALL l rty (FStr fn) args) = filter isFn args
    where
        isFn (desc,_) = case toFType desc of
                            FFunction -> True
                            FFunctionIO -> True
                            _ -> False
hasCallback _ = []

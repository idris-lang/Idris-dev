module RTS.CodegenC where

import Core.TT
import Core.Evaluate
import Core.CaseTree

import RTS.PreC
import RTS.SC
import RTS.Bytecode

import Idris.AbsSyntax

import Data.Char
import Data.List
import Control.Monad.State
import System.Process
import System.IO
import System.Directory
import System.Environment
import System.FilePath ((</>))
import Debug.Trace

import Paths_idris

compileC :: FilePath -> Term -> Idris ()
compileC f tm
    = do checkMVs
         let tmnames = namesUsed (STerm tm)
         used <- mapM (allNames []) tmnames
         i <- get
         let entry = mainFn (idris_scprims i) tm
         scs' <- mkDecls tm (concat used)
         let scs = scs' ++ entry
         objs <- getObjectFiles
         libs <- getLibs
         hdrs <- getHdrs
         ddir <- liftIO $ getDataDir
         -- if any includes exist in the data directory, use that
         hdrs' <- liftIO $ mapM (inDir ddir) hdrs
         let bcs = bcdefs scs
         let pcs = preCdefs bcs
         let code = cdefs pcs
         liftIO $ writeFile (f ++ ".c") code
  where checkMVs = do i <- get
                      case idris_metavars i \\ primDefs of
                            [] -> return ()
                            ms -> fail $ "There are undefined metavariables: " ++ show ms
        inDir d h = do let f = d </> h
                       ex <- doesFileExist f
                       if ex then return f else return h


mainFn ps tm = toSC ps (MN 0 "_main", Function undefined tm)

allNames :: [Name] -> Name -> Idris [Name]
allNames ns n | n `elem` ns = return []
allNames ns n = do i <- get
                   case lookupCtxt Nothing n (idris_callgraph i) of
                      [ns'] -> do more <- mapM (allNames (n:ns)) ns' 
                                  return (nub (n : concat more))
                      _ -> return [n]

mkDecls :: Term -> [Name] -> Idris [(Name, SCDef)]
mkDecls t used
    = do i <- getIState
         let ds = filter (\ (n, d) -> n `elem` used) $ ctxtAlist (tt_ctxt i)
         return $ concatMap (toSC (idris_scprims i)) ds

cdefs :: [(Name, (Int, PreC))] -> String
cdefs xs = concatMap (\ (n, (i, c)) -> proto n) xs ++ "\n" ++
           concatMap (\ (n, (i, c)) -> codegenC n i c) xs

codegenC :: Name -> Int -> PreC -> String
codegenC n args prec 
    = "/* " ++ show prec ++ " */\n\n" ++
      "void " ++ cname n ++ "(VM* vm) {\n" ++
        indent 1 ++ "int i;\n" ++
        concatMap (cg 1) prec ++ "}\n\n"

indent i = take (i * 4) (repeat ' ')

reg RVal = "vm->ret"
reg (LVar v) = "*(vm->valstack_ptr-" ++ show v ++ ")"

catom :: CAtom -> String
catom (CL l) = reg (LVar l) 
catom (CC (I i)) = "MKINT(" ++ show i ++ ")"
catom (CC v) = "const(" ++ show v ++ ")"
catom (CP n i) = "MKCLOSURE(" ++ cname n ++ ", " ++ show i ++ ")"
    
off o (CL i) = CL (i + o)
off o x = x

assignCon i r tag args
   = indent i ++ reg r ++ " = MKCON(" ++ show tag ++ ", " ++ 
                                         show (length args) ++ ");\n" ++
     indent i ++ setArgs 0 args ++ "\n"
  where
    setArgs i [] = ""
    setArgs i (a : as) = "SETARG(" ++ reg r ++ ", " ++
                                      show i ++ ", " ++ catom a ++ "); "
                         ++ setArgs (i + 1) as

assignFn i r f args
   = indent i ++ "EXTEND(" ++ show (length args) ++ ");\n" ++
     indent i ++ setArgs 1 (map (off (length args)) (reverse args)) ++ "\n" ++
     indent i ++ cname f ++ "(vm);\n" ++
     indent i ++ "CLEAR(" ++ show (length args) ++ ");\n" ++
     case r of
        RVal -> ""
        r -> indent i ++ reg r ++ " = " ++ reg RVal ++ "\n"
  where
    setArgs i [] = ""
    setArgs i (a : as) = reg (LVar i) ++ " = " ++ catom a ++ "; "
                         ++ setArgs (i + 1) as

assignClosure i lazy r atom args
    = indent i ++ reg r ++ " = APPLY(" ++ catom atom ++ ", " ++ show (length args) ++
                                    ");\n" ++
      indent i ++ setArgs 0 args ++ "\n" ++
      if not lazy then
          indent i ++ "if (READY(" ++ reg r ++ ")) {\n" ++
          indent (i + 1) ++ reg r ++ " = EVAL(" ++ reg r ++ ");\n" ++
          indent i ++ "} else {\n" ++
          indent (i + 1) ++ "// do nothing \n" ++
          indent i ++ "}\n"
        else ""
  where
    setArgs i [] = ""
    setArgs i (a : as) = "ADDARG(" ++ show i ++ ", " ++ reg r ++ ", " ++ catom a ++ "); "
                         ++ setArgs (i + 1) as

doTailCall i d f args
   = indent i ++ "EXTEND(" ++ show (length args) ++ ");\n" ++
     indent i ++ setArgs 1 (map (off (length args)) (reverse args)) ++ "\n" ++
     indent i ++ "SLIDE(" ++ show d ++ ", " ++ show (length args) ++ ");\n" ++
     indent i ++ cname f ++ "(vm); return;\n" 
  where
    setArgs i [] = ""
    setArgs i (a : as) = reg (LVar i) ++ " = " ++ catom a ++ "; "
                         ++ setArgs (i + 1) as

assignFCall i r cfn rt args
   = indent i ++ reg r ++ " = " ++ fromC rt ++
       "(" ++
           cfn ++ "(" ++ showSep ", " (map toCa args) ++ "))" ++ ";\n"
  where fromC (Just IType) = "MKINT"
        fromC (Just StrType) = "MKSTR"
        fromC _ = "MKVAL"

        toC (Just IType) = "GETINT"
        toC (Just StrType) = "GETSTR"
        toC _ = "GETVAL"

        toCa (a, ty) = toC ty ++ "(" ++ catom a ++ ")" 

assignPrimOp i r p args
    = indent i ++ reg r ++ " = " ++ op p args ++ ";\n"

cg :: Int -> CInst -> String
cg i (ASSIGN r (CCon t args))
   = assignCon i r t args
cg i (ASSIGN r (CExactApp f args))
   = assignFn i r f args
cg i (ASSIGN r (CApp f args))
   = assignClosure i False r f args
cg i (ASSIGN r (CLazy f args))
   = assignClosure i True r f args
cg i (ASSIGN r (CFCall cfn rt args))
   = assignFCall i r cfn rt args
cg i (ASSIGN r (CPrimOp p args))
   = assignPrimOp i r p args
cg i (ASSIGN r (CAtom e)) = indent i ++ reg r ++ " = " ++ catom e ++ ";\n"
cg i (RESERVE s) = indent i ++ "EXTEND(" ++ show s ++ ");\n"
cg i (CLEAR s) = indent i ++ "CLEAR(" ++ show s ++ ");\n"
cg i (EVAL e) = indent i ++ "EVAL(" ++ reg (LVar e) ++ ");\n"
cg i (PROJECT scr loc num)
   = indent i ++ "PROJECT(" ++ reg (LVar scr) ++ ", " ++ 
                               reg (LVar loc) ++ ", " ++ show num ++ ");\n"
cg i (SWITCH v bs def)
   = indent i ++ "switch(" ++ sval v ++ ") {\n" ++
     concatMap branch bs ++
     indent i ++ "default:\n" ++ concatMap (cg (i+1)) def ++
     indent (i+1) ++ "break;\n" ++
     indent i ++ "};\n"
   where sval (CTag l) = "TAG(" ++ reg (LVar l) ++ ")"
         sval (CIntVal l) = "GETINT(" ++ reg (LVar l) ++ ")"

         branch (t, c) = indent i ++ "case " ++ show t ++ ":\n" ++
                         concatMap (cg (i+1)) c ++ 
                         indent (i+1) ++ "break;\n"
cg i (TAILCALL d f args) = assignClosure i False RVal f args -- doTailClosure i d f args 
cg i (TAILCALLEXACT d f args) = doTailCall i d f args 
cg i (ERROR s) = indent i ++ "ERROR(" ++ show s ++ ")\n";
cg i x = trace (show x ++ " not done") $ indent i ++ "NOT DONE;\n"

cname :: Name -> String
cname (UN s) = "_I_" ++ toC s
cname (MN i s) = "_M_I_" ++ show i ++ "_" ++ toC s
cname (NS n ss) = "_" ++ showSep "_" (map toC ss) ++ cname n 

toC s = concatMap special s
  where special c | isAlphaNum c = [c]
                  | c == '_' = "__"
                  | otherwise = "_" ++ show (fromEnum c) ++ "_"

proto :: Name -> String
proto n = "void " ++ cname n ++ "(VM* vm);\n" 

op AddI [l, r] = "INTOP(+, " ++ catom l ++ ", " ++ catom r ++ ")"
op SubI [l, r] = "INTOP(-, " ++ catom l ++ ", " ++ catom r ++ ")"
op MulI [l, r] = "INTOP(*, " ++ catom l ++ ", " ++ catom r ++ ")"
op DivI [l, r] = "INTOP(/, " ++ catom l ++ ", " ++ catom r ++ ")"

op ConcatS [l,r] = "CONCAT(" ++ catom l ++ ", " ++ catom r ++ ")"

op o args = trace (show (op, args) ++ " operator undefined")
                   $ "0 /* Op not defined " ++ show o ++ " */"
            
module RTS.CodegenC where

import Core.TT
import RTS.PreC
import RTS.SC

import Data.Char

cdefs :: [(Name, (Int, PreC))] -> String
cdefs xs = concatMap (\ (n, (i, c)) -> proto n) xs ++ "\n" ++
           concatMap (\ (n, (i, c)) -> codegenC n i c) xs

codegenC :: Name -> Int -> PreC -> String
codegenC n args prec 
    = "void " ++ cname n ++ "(VM* vm) {\n" ++
        concatMap (cg 1) prec ++ "}\n\n"

indent i = take (i * 4) (repeat ' ')

reg RVal = "vm->ret"
reg (LVar v) = "*(vm->stack-" ++ show v ++ ")"

catom :: CAtom -> String
catom (CL l) = reg (LVar l) 
catom (CC (I i)) = "MKINT(" ++ show i ++ ")"
catom (CP n) = cname n

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
     indent i ++ setArgs 1 (reverse args) ++ "\n"
   --  indent i ++ "CALL(" ++ reg r ++ ", " ++ cname f ++ ");\n"
  where
    setArgs i [] = ""
    setArgs i (a : as) = reg (LVar i) ++ " = " ++ catom a ++ "; "
                         ++ setArgs (i + 1) as

tailCall i d f args
   = indent i ++ "EXTEND(" ++ show (length args) ++ ");\n" ++
     indent i ++ setArgs 1 (reverse args) ++ "\n"
--     indent i ++ "TAILCALL(" ++ show d ++ ", " ++ cname f ++ ");\n"
  where
    setArgs i [] = ""
    setArgs i (a : as) = reg (LVar i) ++ " = " ++ catom a ++ "; "
                         ++ setArgs (i + 1) as

cg :: Int -> CInst -> String
cg i (ASSIGN r (CCon t args))
   = assignCon i r t args
cg i (ASSIGN r (CApp f args))
   = assignFn i r f args
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
cg i (TAILCALL d f args) = tailCall i d f args 
cg i (ERROR s) = indent i ++ "ERROR(" ++ show s ++ ")\n";
cg i _ = indent i ++ "NOT DONE;\n"

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


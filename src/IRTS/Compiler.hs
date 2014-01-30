{-# LANGUAGE PatternGuards, TypeSynonymInstances, CPP #-}

module IRTS.Compiler where

import IRTS.Lang
import IRTS.Defunctionalise
import IRTS.Simplified
import IRTS.CodegenCommon
import IRTS.CodegenC
import IRTS.CodegenJava
import IRTS.DumpBC
import IRTS.CodegenJavaScript
#ifdef IDRIS_LLVM
import IRTS.CodegenLLVM
#else
import Util.LLVMStubs
#endif
import IRTS.Inliner

import Idris.AbsSyntax
import Idris.UnusedArgs
import Idris.Error

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.CaseTree

import Control.Monad.State
import Data.List
import System.Process
import System.IO
import System.Directory
import System.Environment
import System.FilePath ((</>), addTrailingPathSeparator)

import Paths_idris

compile :: Codegen -> FilePath -> Term -> Idris ()
compile codegen f tm
   = do checkMVs
        let tmnames = namesUsed (STerm tm)
        usedIn <- mapM (allNames []) tmnames
        let used = [sUN "prim__subBigInt", sUN "prim__addBigInt"] : usedIn
        defsIn <- mkDecls tm (concat used)
        findUnusedArgs (concat used)
        maindef <- irMain tm
        objs <- getObjectFiles codegen
        libs <- getLibs codegen
        flags <- getFlags codegen
        hdrs <- getHdrs codegen
        impdirs <- allImportDirs
        let defs = defsIn ++ [(sMN 0 "runMain", maindef)]
        -- iputStrLn $ showSep "\n" (map show defs)
        let (nexttag, tagged) = addTags 65536 (liftAll defs)
        let ctxtIn = addAlist tagged emptyContext
        iLOG "Defunctionalising"
        let defuns_in = defunctionalise nexttag ctxtIn
        logLvl 5 $ show defuns_in
        iLOG "Inlining"
        let defuns = inline defuns_in
        logLvl 5 $ show defuns
        iLOG "Resolving variables for CG"
        -- iputStrLn $ showSep "\n" (map show (toAlist defuns))
        let checked = checkDefs defuns (toAlist defuns)
        outty <- outputTy
        dumpCases <- getDumpCases
        dumpDefun <- getDumpDefun
        case dumpCases of
            Nothing -> return ()
            Just f -> runIO $ writeFile f (showCaseTrees defs)
        case dumpDefun of
            Nothing -> return ()
            Just f -> runIO $ writeFile f (dumpDefuns defuns)
        triple <- targetTriple
        cpu <- targetCPU
        optimize <- optLevel
        iLOG "Building output"
        case checked of
            OK c -> runIO $ case codegen of
                              ViaC ->
                                  codegenC c f outty hdrs
                                    (concatMap mkObj objs)
                                    (concatMap mkLib libs)
                                    (concatMap mkFlag flags ++
                                     concatMap incdir impdirs) NONE
                              ViaJava ->
                                  codegenJava [] c f hdrs libs outty
                              ViaJavaScript ->
                                  codegenJavaScript JavaScript c f outty
                              ViaNode ->
                                  codegenJavaScript Node c f outty
                              ViaLLVM -> codegenLLVM c triple cpu optimize f outty
                              Bytecode -> dumpBC c f
            Error e -> ierror e
  where checkMVs = do i <- getIState
                      case map fst (idris_metavars i) \\ primDefs of
                            [] -> return ()
                            ms -> ifail $ "There are undefined metavariables: " ++ show ms
        inDir d h = do let f = d </> h
                       ex <- doesFileExist f
                       if ex then return f else return h
        mkObj f = f ++ " "
        mkLib l = "-l" ++ l ++ " "
        mkFlag l = l ++ " "

        incdir i = "-I" ++ i ++ " "


irMain :: TT Name -> Idris LDecl
irMain tm = do i <- ir tm
               return $ LFun [] (sMN 0 "runMain") [] (LForce i)

mkDecls :: Term -> [Name] -> Idris [(Name, LDecl)]
mkDecls t used
    = do i <- getIState
         let ds = filter (\ (n, d) -> n `elem` used || isCon d) $ ctxtAlist (tt_ctxt i)
         mapM traceUnused used
         decls <- mapM build ds
         return decls

showCaseTrees :: [(Name, LDecl)] -> String
showCaseTrees ds = showSep "\n\n" (map showCT ds)
  where
    showCT (n, LFun _ f args lexp)
       = show n ++ " " ++ showSep " " (map show args) ++ " =\n\t "
            ++ show lexp
    showCT (n, LConstructor c t a) = "data " ++ show n ++ " " ++ show a

isCon (TyDecl _ _) = True
isCon _ = False

class ToIR a where
    ir :: a -> Idris LExp

build :: (Name, Def) -> Idris (Name, LDecl)
build (n, d)
    = do i <- getIState
         case lookup n (idris_scprims i) of
              Just (ar, op) ->
                  let args = map (\x -> sMN x "op") [0..] in
                      return (n, (LFun [] n (take ar args)
                                         (LOp op (map (LV . Glob) (take ar args)))))
              _ -> do def <- mkLDecl n d
                      logLvl 3 $ "Compiled " ++ show n ++ " =\n\t" ++ show def
                      return (n, def)

getPrim :: IState -> Name -> [LExp] -> Maybe LExp
getPrim i n args = case lookup n (idris_scprims i) of
                        Just (ar, op) ->
                           if (ar == length args)
                             then return (LOp op args)
                             else Nothing
                        _ -> Nothing

declArgs args inl n (LLam xs x) = declArgs (args ++ xs) inl n x
declArgs args inl n x = LFun (if inl then [Inline] else []) n args x

mkLDecl n (Function tm _) = do e <- ir tm
                               return (declArgs [] True n e)
mkLDecl n (CaseOp ci _ _ _ pats cd)
   = let (args, sc) = cases_runtime cd in
         do e <- ir (args, sc)
            return (declArgs [] (case_inlinable ci) n e)
mkLDecl n (TyDecl (DCon t a) _) = return $ LConstructor n t a
mkLDecl n (TyDecl (TCon t a) _) = return $ LConstructor n (-1) a
mkLDecl n _ = return (LFun [] n [] (LError ("Impossible declaration " ++ show n)))

instance ToIR (TT Name) where
    ir tm = ir' [] tm where
      ir' env tm@(App f a)
          | (P _ (UN m) _, args) <- unApply tm,
            m == txt "mkForeignPrim"
              = doForeign env args
          | (P _ (UN u) _, [_, arg]) <- unApply tm,
            u == txt "unsafePerformPrimIO"
              = ir' env arg
            -- TMP HACK - until we get inlining.
          | (P _ (UN r) _, [_, _, _, _, _, arg]) <- unApply tm,
            r == txt "replace"
              = ir' env arg
          | (P _ (UN l) _, [_, arg]) <- unApply tm,
            l == txt "lazy"
              = do arg' <- ir' env arg
                   return $ LLazyExp arg'
          | (P _ (UN a) _, [_, _, _, arg]) <- unApply tm,
            a == txt "assert_smaller"
              = ir' env arg
          | (P _ (UN p) _, [_, arg]) <- unApply tm,
            p == txt "par"
              = do arg' <- ir' env arg
                   return $ LOp LPar [LLazyExp arg']
          | (P _ (UN pf) _, [arg]) <- unApply tm,
            pf == txt "prim_fork"
              = do arg' <- ir' env arg
                   return $ LOp LFork [LLazyExp arg']
          | (P _ (UN m) _, [_,size,t]) <- unApply tm,
            m == txt "malloc"
              = do size' <- ir' env size
                   t' <- ir' env t
                   return t' -- TODO $ malloc_ size' t'
          | (P _ (UN tm) _, [_,t]) <- unApply tm,
            tm == txt "trace_malloc"
              = do t' <- ir' env t
                   return t' -- TODO
--           | (P _ (NS (UN "S") ["Nat", "Prelude"]) _, [k]) <- unApply tm
--               = do k' <- ir' env k
--                    return (LOp LBPlus [k', LConst (BI 1)])
          | (P (DCon t a) n _, args) <- unApply tm
              = irCon env t a n args
          | (P (TCon t a) n _, args) <- unApply tm
              = return LNothing
          | (P _ n _, args) <- unApply tm
              = do i <- getIState
                   args' <- mapM (ir' env) args
                   case getPrim i n args' of
                        Just tm -> return tm
                        _ -> do
                                 let collapse
                                        = case lookupCtxtExact n
                                                   (idris_optimisation i) of
                                               Just oi -> collapsible oi
                                               _ -> False
                                 let unused
                                        = case lookupCtxtExact n
                                                      (idris_callgraph i) of
                                               Just (CGInfo _ _ _ _ unusedpos) ->
                                                         unusedpos
                                               _ -> []
                                 if collapse
                                     then return LNothing
                                     else return (LApp False (LV (Glob n))
                                                 (mkUnused unused 0 args'))
          | (f, args) <- unApply tm
              = do f' <- ir' env f
                   args' <- mapM (ir' env) args
                   return (LApp False f' args')
        where mkUnused u i [] = []
              mkUnused u i (x : xs) | i `elem` u = LNothing : mkUnused u (i + 1) xs
                                    | otherwise = x : mkUnused u (i + 1) xs
--       ir' env (P _ (NS (UN "Z") ["Nat", "Prelude"]) _)
--                         = return $ LConst (BI 0)
      ir' env (P _ n _) = return $ LV (Glob n)
      ir' env (V i)     | i >= 0 && i < length env = return $ LV (Glob (env!!i))
                        | otherwise = ifail $ "IR fail " ++ show i ++ " " ++ show tm
      ir' env (Bind n (Lam _) sc)
          = do let n' = uniqueName n env
               sc' <- ir' (n' : env) sc
               return $ LLam [n'] sc'
      ir' env (Bind n (Let _ v) sc)
          = do sc' <- ir' (n : env) sc
               v' <- ir' env v
               return $ LLet n v' sc'
      ir' env (Bind _ _ _) = return $ LNothing
      ir' env (Proj t i) | i == -1
                             = do t' <- ir' env t
                                  return $ LOp (LMinus (ATInt ITBig)) 
                                               [t', LConst (BI 1)]
      ir' env (Proj t i) = do t' <- ir' env t
                              return $ LProj t' i
      ir' env (Constant c) = return $ LConst c
      ir' env (TType _) = return $ LNothing
      ir' env Erased = return $ LNothing
      ir' env Impossible = return $ LNothing
--       ir' env _ = return $ LError "Impossible"

      irCon env t arity n args
        | length args == arity = buildApp env (LV (Glob n)) args
        | otherwise = let extra = satArgs (arity - length args) in
                          do sc' <- irCon env t arity n
                                        (args ++ map (\n -> P Bound n undefined) extra)
                             return $ LLam extra sc'

      satArgs n = map (\i -> sMN i "sat") [1..n]

      buildApp env e [] = return e
      buildApp env e xs = do xs' <- mapM (ir' env) xs
                             return $ LApp False e xs'

      doForeign :: [Name] -> [TT Name] -> Idris LExp
      doForeign env (_ : fgn : args)
         | (_, (Constant (Str fgnName) : fgnArgTys : ret : [])) <- unApply fgn
              = let maybeTys = getFTypes fgnArgTys
                    rty = mkIty' ret in
                case maybeTys of
                  Nothing -> ifail $ "Foreign type specification is not a constant list: " ++ show (fgn:args)
                  Just tys -> do
                    args' <- mapM (ir' env) (init args)
                    -- wrap it in a prim__IO
                    -- return $ con_ 0 @@ impossible @@
                    return $ -- LLazyExp $
                      LForeign LANG_C rty fgnName (zip tys args')
         | otherwise = ifail "Badly formed foreign function call"

getFTypes :: TT Name -> Maybe [FType]
getFTypes tm = case unApply tm of
                 (nil, []) -> Just []
                 (cons, [ty, xs]) ->
                     fmap (mkIty' ty :) (getFTypes xs)
                 _ -> Nothing

mkIty' (P _ (UN ty) _) = mkIty (str ty)
mkIty' (App (P _ (UN fi) _) (P _ (UN intTy) _))
   | fi == txt "FIntT" = mkIntIty (str intTy)
mkIty' (App (App (P _ (UN ff) _) _) (App (P _ (UN fa) _) (App (P _ (UN io) _) _))) 
   | ff == txt "FFunction" && fa == txt "FAny" &&
     io == txt "IO" 
        = FFunctionIO
mkIty' (App (App (P _ (UN ff) _) _) _) 
   | ff == txt "FFunction" = FFunction
mkIty' _ = FAny

-- would be better if these FInt types were evaluated at compile time
-- TODO: add %eval directive for such things

mkIty "FFloat"      = FArith ATFloat
mkIty "FInt"        = mkIntIty "ITNative"
mkIty "FChar"       = mkIntIty "ITChar"
mkIty "FByte"       = mkIntIty "IT8"
mkIty "FShort"      = mkIntIty "IT16"
mkIty "FLong"       = mkIntIty "IT64"
mkIty "FBits8"      = mkIntIty "IT8"
mkIty "FBits16"     = mkIntIty "IT16"
mkIty "FBits32"     = mkIntIty "IT32"
mkIty "FBits64"     = mkIntIty "IT64"
mkIty "FString"     = FString
mkIty "FPtr"        = FPtr
mkIty "FUnit"       = FUnit
mkIty "FFunction"   = FFunction
mkIty "FFunctionIO" = FFunctionIO
mkIty "FBits8x16"   = FArith (ATInt (ITVec IT8 16))
mkIty "FBits16x8"   = FArith (ATInt (ITVec IT16 8))
mkIty "FBits32x4"   = FArith (ATInt (ITVec IT32 4))
mkIty "FBits64x2"   = FArith (ATInt (ITVec IT64 2))
mkIty x             = error $ "Unknown type " ++ x

mkIntIty "ITNative" = FArith (ATInt ITNative)
mkIntIty "ITChar" = FArith (ATInt ITChar)
mkIntIty "IT8"  = FArith (ATInt (ITFixed IT8))
mkIntIty "IT16" = FArith (ATInt (ITFixed IT16))
mkIntIty "IT32" = FArith (ATInt (ITFixed IT32))
mkIntIty "IT64" = FArith (ATInt (ITFixed IT64))

zname = sNS (sUN "Z") ["Nat","Prelude"]
sname = sNS (sUN "S") ["Nat","Prelude"]

instance ToIR ([Name], SC) where
    ir (args, tree) = do logLvl 3 $ "Compiling " ++ show args ++ "\n" ++ show tree
                         tree' <- ir tree
                         return $ LLam args tree'

instance ToIR SC where
    ir t = ir' t where

        ir' (STerm t) = ir t
        ir' (UnmatchedCase str) = return $ LError str
        ir' (ProjCase tm alts) = do tm' <- ir tm
                                    alts' <- mapM (mkIRAlt tm') alts
                                    return $ LCase tm' alts'
        ir' (Case n alts) = do alts' <- mapM (mkIRAlt (LV (Glob n))) alts
                               return $ LCase (LV (Glob n)) alts'
        ir' ImpossibleCase = return LNothing

        -- special cases for Z and S
        -- Needs rethink: projections make this fail
--         mkIRAlt n (ConCase z _ [] rhs) | z == zname
--              = mkIRAlt n (ConstCase (BI 0) rhs)
--         mkIRAlt n (ConCase s _ [arg] rhs) | s == sname
--              = do n' <- ir n
--                   rhs' <- ir rhs
--                   return $ LDefaultCase
--                               (LLet arg (LOp LBMinus [n', LConst (BI 1)])
--                                           rhs')
        mkIRAlt _ (ConCase n t args rhs)
             = do rhs' <- ir rhs
                  return $ LConCase (-1) n args rhs'
        mkIRAlt _ (ConstCase x rhs)
          | matchable x
             = do rhs' <- ir rhs
                  return $ LConstCase x rhs'
          | matchableTy x
             = do rhs' <- ir rhs
                  return $ LDefaultCase rhs'
        mkIRAlt tm (SucCase n rhs)
           = do rhs' <- ir rhs
                return $ LDefaultCase (LLet n (LOp (LMinus (ATInt ITBig))
                                                 [tm,
                                                  LConst (BI 1)]) rhs')
--                 return $ LSucCase n rhs'
        mkIRAlt _ (ConstCase c rhs)
           = ifail $ "Can't match on (" ++ show c ++ ")"
        mkIRAlt _ (DefaultCase rhs)
           = do rhs' <- ir rhs
                return $ LDefaultCase rhs'

        matchable (I _) = True
        matchable (BI _) = True
        matchable (Ch _) = True
        matchable (Str _) = True
        matchable _ = False

        matchableTy (AType (ATInt ITNative)) = True
        matchableTy (AType (ATInt ITBig)) = True
        matchableTy (AType (ATInt ITChar)) = True
        matchableTy StrType = True

        matchableTy (AType (ATInt (ITFixed IT8)))  = True
        matchableTy (AType (ATInt (ITFixed IT16))) = True
        matchableTy (AType (ATInt (ITFixed IT32))) = True
        matchableTy (AType (ATInt (ITFixed IT64))) = True

        matchableTy _ = False


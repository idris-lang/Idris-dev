{-# LANGUAGE PatternGuards #-}

module Idris.Compiler where

import Idris.AbsSyntax
import Core.TT

{-
import Idris.Transforms

import Core.Evaluate
import Core.CaseTree

import Control.Monad.State
import Data.List
import System.Process
import System.IO
import System.Directory
import System.Environment

import Paths_idris

import Epic.Epic hiding (Term, Type, Name, fn, compile)
import qualified Epic.Epic as E
-}

compileEpic :: FilePath -> Term -> Idris ()
compileEpic f t = fail "Epic backend disabled"

{-
compile f tm
    = do checkMVs
         let tmnames = namesUsed (STerm tm)
         used <- mapM (allNames []) tmnames
         ds <- mkDecls tm (concat used)
         objs <- getObjectFiles
         libs <- getLibs
         hdrs <- getHdrs
         ddir <- liftIO $ getDataDir
         -- if any includes exist in the data directory, use that
         hdrs' <- liftIO $ mapM (inDir ddir) hdrs
         let incs = map Include hdrs'
         so <- getSO
--          let ilib = ddir ++ "/libidris.a"
         case so of
            Nothing ->
                do m <- epicMain tm
                   let mainval = EpicFn (name "main") m
                   liftIO $ compileObjWith [] 
                                (mkProgram (incs ++ mainval : ds)) (f ++ ".o")
                   liftIO $ link ((f ++ ".o") : objs ++ (map ("-l"++) libs)) f
  where checkMVs = do i <- get
                      case idris_metavars i \\ primDefs of
                            [] -> return ()
                            ms -> fail $ "There are undefined metavariables: " ++ show ms
        inDir d h = do let f = d ++ "/" ++ h
                       ex <- doesFileExist f
                       if ex then return f else return h


allNames :: [Name] -> Name -> Idris [Name]
allNames ns n | n `elem` ns = return []
allNames ns n = do i <- get
                   case lookupCtxt Nothing n (idris_callgraph i) of
                      [ns'] -> do more <- mapM (allNames (n:ns)) ns' 
                                  return (nub (n : concat more))
                      _ -> return [n]

mkDecls :: Term -> [Name] -> Idris [EpicDecl]
mkDecls t used
    = do i <- getIState
         let ds = filter (\ (n, d) -> n `elem` used) $ ctxtAlist (tt_ctxt i)
         decls <- mapM build ds
         return $ basic_defs ++ decls
             
-- EpicFn (name "main") epicMain : decls

ename x = name ("idris_" ++ show x)
aname x = name ("a_" ++ show x)

epicMain tm = do e <- epic tm
                 return $ effect_ e

-- epicMain = effect_ $ -- ref (ename (UN "run__IO")) @@
--                      ref (ename (NS (UN "main") ["main"]))

class ToEpic a where
    epic :: a -> Idris E.Term

build :: (Name, Def) -> Idris EpicDecl
build (n, d) = do i <- getIState
                  case lookup n (idris_prims i) of
                    Just opDef -> return $ EpicFn (ename n) opDef
                    _ ->       do def <- epic d
                                  logLvl 3 $ "Compiled " ++ show n ++ " =\n\t" ++ show def
                                  return $ EpicFn (ename n) def

impossible = int 42424242

instance ToEpic Def where
    epic (Function tm _) = epic tm
    epic (CaseOp _ _ pats _ _ args sc) = epic (args, sc) -- optimised version
    epic _ = return impossible

instance ToEpic (TT Name) where
    epic tm = epic' [] tm where
      epic' env tm@(App f a)
          | (P _ (UN "mkForeign") _, args) <- unApply tm
              = doForeign False args
          | (P _ (UN "mkLazyForeign") _, args) <- unApply tm
              = doForeign True args
          | (P _ (UN "unsafePerformIO") _, [_, arg]) <- unApply tm
              = epic' env arg
          | (P _ (UN "lazy") _, [_,arg]) <- unApply tm
              = do arg' <- epic' env arg
                   return $ lazy_ arg'
          | (P _ (UN "prim__IO") _, [v]) <- unApply tm
              = do v' <- epic' env v
                   return (effect_ v')
          | (P _ (UN "io_bind") _, [_,_,v,k]) <- unApply tm
              = do v' <- epic' env v 
                   k' <- epic' env k
                   return (effect_ (k' @@ (effect_ v')))
          | (P _ (UN "malloc") _, [_,size,t]) <- unApply tm
              = do size' <- epic' env size
                   t' <- epic' env t
                   return $ malloc_ size' t'
          | (P _ (UN "trace_malloc") _, [_,t]) <- unApply tm
              = do t' <- epic' env t
                   return $ mallocTrace_ t'
          | (P (DCon t a) n _, args) <- unApply tm
              = epicCon env t a n args
      epic' env (P (DCon t a) n _) = return $ con_ t
      epic' env (P (TCon t a) n _) = return $ con_ t
      epic' env (P _ n _)          = return $ ref (ename n) 
      epic' env (V i)              = return $ ref (env!!i)
      epic' env (Bind n (Lam _) sc)
            = do sc' <- epic' (aname n : env) sc
                 return $ term ([aname n], sc')
      epic' env (Bind n (Let _ v) sc)
            = do sc' <- epic' (aname n : env) sc
                 v' <- epic' env v
                 return $ let_ v' (aname n, sc') 
      epic' env (Bind _ _ _) = return impossible
      epic' env (App f a) = do f' <- epic' env f
                               a' <- epic' env a
                               return (f' @@ a')
      epic' env (Constant c) = epic c
      epic' env Erased       = return impossible
      epic' env (TType _)      = return impossible

      epicCon env t arity n args
        | length args == arity = buildApp env (con_ t) args
        | otherwise = let extra = satArgs (arity - length args) in
                          do sc' <- epicCon env t arity n 
                                        (args ++ map (\n -> P Bound n undefined) extra)
                             return $ term (map ename extra, sc')
        
      satArgs n = map (\i -> MN i "sat") [1..n]

      buildApp env e [] = return e
      buildApp env e (x:xs) = do x' <- epic' env x
                                 buildApp env (e @@ x') xs
                                    

doForeign :: Bool -> [TT Name] -> Idris E.Term
doForeign lazy (_ : fgn : args)
   | (_, (Constant (Str fgnName) : fgnArgTys : ret : [])) <- unApply fgn
        = let tys = getFTypes fgnArgTys
              rty = mkEty' ret in
              do args' <- mapM epic args
                 -- wrap it in a prim__IO
                 -- return $ con_ 0 @@ impossible @@ 
                 if lazy 
                   then return $ lazy_ $ foreignL_ rty fgnName (zip args' tys)
                   else return $ lazy_ $ foreign_ rty fgnName (zip args' tys)
   | otherwise = fail "Badly formed foreign function call"

getFTypes :: TT Name -> [E.Type]
getFTypes tm = case unApply tm of
                 (nil, []) -> []
                 (cons, [ty, xs]) -> 
                    let rest = getFTypes xs in
                        mkEty' ty : rest

mkEty' (P _ (UN ty) _) = mkEty ty
mkEty' _ = tyAny

mkEty "FInt"    = tyInt
mkEty "FFloat"  = tyFloat
mkEty "FChar"   = tyChar
mkEty "FString" = tyString
mkEty "FPtr"    = tyPtr
mkEty "FUnit"   = tyUnit

instance ToEpic Const where
    epic (I i)   = return (int i)
    epic (BI i)  = return (bigint i)
    epic (Fl f)  = return (float f)
    epic (Str s) = return (str s)
    epic (Ch c)  = return (char c)
    epic IType   = return $ con_ 1
    epic FlType  = return $ con_ 2
    epic ChType  = return $ con_ 3
    epic StrType = return $ con_ 4
    epic PtrType = return $ con_ 5
    epic BIType  = return $ con_ 6

instance ToEpic ([Name], SC) where
    epic (args, tree) = do logLvl 3 $ "Compiling " ++ show args ++ "\n" ++ show tree
                           tree' <- epic tree
                           return $ term (map ename args, tree')

instance ToEpic SC where
    epic (Case n [ConCase _ i ns sc])
        = epicLet n ns 0 sc
      where
        epicLet x [] _ sc = epic sc
        epicLet x (n:ns) i sc 
            = do sc' <- epicLet x ns (i+1) sc
                 return $ let_ (ref (ename x) !. i) (ename n, sc')

    epic (STerm t) = epic t
    epic (UnmatchedCase str) = return $ error_ str
    epic (Case n alts) = do alts' <- mapM mkEpicAlt alts
                            return $ case_ (ref (ename n)) alts'
      where
        mkEpicAlt (ConCase n t args rhs) = do rhs' <- epic rhs
                                              return $ con t (map ename args, rhs')
        mkEpicAlt (ConstCase (I i) rhs)  = do rhs' <- epic rhs
                                              return $ constcase i rhs'
        mkEpicAlt (ConstCase IType rhs) = do rhs' <- epic rhs 
                                             return $ defaultcase rhs'
        mkEpicAlt (ConstCase c rhs)      
           = fail $ "Can only pattern match on integer constants (" ++ show c ++ ")"
        mkEpicAlt (DefaultCase rhs)      = do rhs' <- epic rhs
                                              return $ defaultcase rhs'

-}

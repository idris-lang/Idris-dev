{-# LANGUAGE PatternGuards #-}

module Idris.Compiler where

import Idris.AbsSyntax

import Core.TT
import Core.Evaluate
import Core.CaseTree

import Control.Monad.State
import Data.List
import System.Process
import System.IO
import System.Directory
import System.Environment

import Epic.Epic hiding (Term, Type, Name, fn, compile)
import qualified Epic.Epic as E

primDefs = [UN "mkForeign", UN "FalseElim"]

compile :: FilePath -> Term -> Idris ()
compile f tm
    = do checkMVs
         ds <- mkDecls tm
         objs <- getObjectFiles
         libs <- getLibs
         hdrs <- getHdrs
         let incs = map Include hdrs
         so <- getSO
         case so of
            Nothing ->
                do m <- epicMain tm
                   let mainval = EpicFn (name "main") m
                   liftIO $ compileObjWith [Debug] 
                                (mkProgram (incs ++ mainval : ds)) (f ++ ".o")
                   liftIO $ link ((f ++ ".o") : objs ++ (map ("-l"++) libs)) f
  where checkMVs = do i <- get
                      case idris_metavars i \\ primDefs of
                            [] -> return ()
                            ms -> fail $ "There are undefined metavariables: " ++ show ms

mkDecls :: Term -> Idris [EpicDecl]
mkDecls t = do i <- getIState
               decls <- mapM build (ctxtAlist (tt_ctxt i))
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
              = doForeign args
          | (P _ (UN "lazy") _, [_,arg]) <- unApply tm
              = do arg' <- epic' env arg
                   return $ lazy_ arg'
          | (P _ (UN "prim__IO") _, [v]) <- unApply tm
              = epic' env v
          | (P _ (UN "io_bind") _, [_,_,v,k]) <- unApply tm
              = do v' <- epic' env v 
                   k' <- epic' env k
                   return (k' @@ (effect_ v'))
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
      epic' env (Set _)      = return impossible

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
                                    

doForeign :: [TT Name] -> Idris E.Term
doForeign (_ : fgn : args)
   | (_, (Constant (Str fgnName) : fgnArgTys : P _ (UN ret) _ : [])) <- unApply fgn
        = let tys = getFTypes fgnArgTys
              rty = mkEty ret in
              do args' <- mapM epic args
                 -- wrap it in a prim__IO
                 -- return $ con_ 0 @@ impossible @@ 
                 return $ lazy_ $ foreign_ rty fgnName (zip args' tys)
   | otherwise = fail "Badly formed foreign function call"

getFTypes :: TT Name -> [E.Type]
getFTypes tm = case unApply tm of
                 (nil, []) -> []
                 (cons, [(P _ (UN ty) _), xs]) -> 
                    let rest = getFTypes xs in
                        mkEty ty : rest                        

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

tempfile :: IO (FilePath, Handle)
tempfile = do env <- environment "TMPDIR"
              let dir = case env of
                              Nothing -> "/tmp"
                              (Just d) -> d
              openTempFile dir "esc"

environment :: String -> IO (Maybe String)
environment x = catch (do e <- getEnv x
                          return (Just e))
                      (\_ -> return Nothing)


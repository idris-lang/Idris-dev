{-# LANGUAGE PatternGuards #-}

module Idris.Compiler where

import Idris.AbsSyntax

import Core.TT
import Core.Evaluate
import Core.CaseTree

import Control.Monad.State

import Epic.Epic hiding (Term, Type, Name, fn, compile)
import qualified Epic.Epic as E

primDefs = [UN ["mkForeign"]]

compile :: FilePath -> Idris ()
compile f = do ds <- mkDecls
               lift $ compileWith [Debug] (mkProgram ds) f 

mkDecls :: Idris [EpicDecl]
mkDecls = do i <- getIState
             decls <- mapM build (toAlist (tt_ctxt i))
             return $ basic_defs ++ EpicFn (name "main") epicMain : decls

ename x = name ("idris_" ++ show x)
aname x = name ("a_" ++ show x)

epicMain = ref (ename (UN ["main"]))

class ToEpic a where
    epic :: a -> Idris E.Term

build :: (Name, Def) -> Idris EpicDecl
build (n, d) = do i <- getIState
                  case lookup n (idris_prims i) of
                    Just opDef -> return $ EpicFn (ename n) opDef
                    _ ->       do def <- epic d
                                  return $ EpicFn (ename n) def

impossible = int 42424242

instance ToEpic Def where
    epic (Function (Fun _ _ tm _)) = epic tm
    epic (CaseOp _ pats args sc)   = epic (args, sc) -- TODO: redo case comp after optimising
    epic _ = return impossible

instance ToEpic (TT Name) where
    epic tm = epic' [] tm where
      epic' env tm@(App f a)
          | (P _ (UN ["mkForeign"]) _, args) <- unApply tm
              = doForeign args
      epic' env (P (DCon t a) n _) = return $ con_ t
      epic' env (P (TCon t a) n _) = return $ con_ t
      epic' env (P _ n _) = return $ ref (ename n) 
      epic' env (V i) = return $ ref (env!!i)
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
                               logLvl 3 $ "Compiled " ++ show f ++ " @@ " ++ show a
                               return (f' @@ a')
      epic' env (Constant c) = epic c
      epic' env (Set _) = return impossible

doForeign :: [TT Name] -> Idris E.Term
doForeign (_ : fgn : args)
   | (_, (Constant (Str fgnName) : fgnArgTys : P _ (UN [ret]) _ : [])) <- unApply fgn
        = let tys = getFTypes fgnArgTys
              rty = mkEty ret in
              do args' <- mapM epic args
                 -- wrap it in a prim__IO
                 return $ con_ 0 @@ impossible @@ foreign_ rty fgnName (zip args' tys)
   | otherwise = fail "Badly formed foreign function call"

getFTypes :: TT Name -> [E.Type]
getFTypes tm = case unApply tm of
                 (nil, [arg]) -> []
                 (cons, [a, (P _ (UN [ty]) _), xs]) -> 
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
    epic (Fl f)  = return (float f)
    epic (Str s) = return (str s)
    epic (Ch c)  = return (char c)
    epic IType   = return $ con_ 1
    epic FlType  = return $ con_ 2
    epic ChType  = return $ con_ 3
    epic StrType = return $ con_ 4
    epic PtrType = return $ con_ 5

instance ToEpic ([Name], SC) where
    epic (args, tree) = do logLvl 3 $ "Compiling " ++ show args ++ "\n" ++ show tree
                           tree' <- epic tree
                           return $ term (map ename args, tree')

instance ToEpic SC where
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



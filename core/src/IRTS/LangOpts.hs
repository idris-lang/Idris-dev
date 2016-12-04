{-|
Module      : IRTS.LangOpts
Description : Transformations to apply to Idris' IR.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE DeriveFunctor, PatternGuards #-}

module IRTS.LangOpts where

import Idris.Core.CaseTree
import Idris.Core.TT
import IRTS.Lang

import Control.Applicative hiding (Const)
import Control.Monad.State hiding (lift)
import Data.List
import Debug.Trace

inlineAll :: [(Name, LDecl)] -> [(Name, LDecl)]
inlineAll lds = let defs = addAlist lds emptyContext in
                    map (\ (n, def) -> (n, doInline defs def)) lds

nextN :: State Int Name
nextN = do i <- get
           put (i + 1)
           return $ sMN i "in"

-- | Inline inside a declaration.
--
-- Variables are still Name at this stage.  Need to preserve
-- uniqueness of variable names in the resulting definition, so invent
-- a new name for every variable we encounter
doInline :: LDefs -> LDecl -> LDecl
doInline defs d@(LConstructor _ _ _) = d
doInline defs (LFun opts topn args exp)
      = let res = evalState (inlineWith [topn] (map (\n -> (n, LV (Glob n))) args) exp) 0 in
            LFun opts topn args res
  where
    inlineWith :: [Name] -> [(Name, LExp)] -> LExp -> State Int LExp
    inlineWith done env var@(LV (Glob n))
                                     = case lookup n env of
                                            Just t -> return t
                                            Nothing -> return var
    inlineWith done env (LLazyApp n es) = LLazyApp n <$> (mapM (inlineWith done env) es)
    inlineWith done env (LForce e) = LForce <$> inlineWith done env e
    inlineWith done env (LLazyExp e) = LLazyExp <$> inlineWith done env e
    -- Extend the environment for Let and Lam so that bound names aren't
    -- expanded with any top level argument definitions they shadow
    inlineWith done env (LLet n val sc)
       = do n' <- nextN
            LLet n' <$> inlineWith done env val <*>
                        inlineWith done ((n, LV (Glob n')) : env) sc
    inlineWith done env (LLam args sc)
       = do ns' <- mapM (\n -> do n' <- nextN
                                  return (n, n')) args
            LLam (map snd ns') <$>
                 inlineWith done (map (\ (n,n') -> (n, LV (Glob n'))) ns' ++ env) sc
    inlineWith done env (LProj exp i) = LProj <$> inlineWith done env exp <*> return i
    inlineWith done env (LCon loc i n es)
       = LCon loc i n <$> mapM (inlineWith done env) es
    inlineWith done env (LCase ty e alts)
       = LCase ty <$> inlineWith done env e <*> mapM (inlineWithAlt done env) alts
    inlineWith done env (LOp f es) = LOp f <$> mapM (inlineWith done env) es
    -- the interesting case!
    inlineWith done env (LApp t (LV (Glob n)) es)
       | n `notElem` done,
         [LFun opts _ args body] <- lookupCtxt n defs,
         Inline `elem` opts,
         length es == length args
           = do es' <- mapM (inlineWith done env) es
                inlineWith (n : done) (zip args es' ++ env) body
    inlineWith done env (LApp t f es)
       = LApp t <$> inlineWith done env f <*> mapM (inlineWith done env) es
    inlineWith done env (LForeign t s args)
       = LForeign t s <$> mapM (\(t, e) -> do e' <- inlineWith done env e
                                              return (t, e')) args
    inlineWith done env t = return t

    inlineWithAlt done env (LConCase i n es rhs)
       = do ns' <- mapM (\n -> do n' <- nextN
                                  return (n, n')) es
            LConCase i n (map snd ns') <$>
              inlineWith done (map (\ (n,n') -> (n, LV (Glob n'))) ns' ++ env) rhs
    inlineWithAlt done env (LConstCase c e) = LConstCase c <$> inlineWith done env e
    inlineWithAlt done env (LDefaultCase e) = LDefaultCase <$> inlineWith done env e

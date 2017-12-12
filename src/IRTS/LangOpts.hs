{-|
Module      : IRTS.LangOpts
Description : Transformations to apply to Idris' IR.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE DeriveFunctor, PatternGuards #-}

module IRTS.LangOpts(inlineAll) where

import Idris.Core.CaseTree
import Idris.Core.TT
import IRTS.Lang

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
      = let res = evalState (eval [] initEnv [topn] defs exp)
                            (length args) in
--       = let res = evalState (inlineWith [topn] (map (\n -> (n, LV n)) args) exp) 0 in
            case res of
                 LLam args' body -> LFun opts topn (map snd initNames ++ args') body
                 _ -> LFun opts topn (map snd initNames) res
  where
    initNames = zipWith (\n i -> (n, newn n i)) args [0..]
    initEnv = map (\(n, n') -> (n, LV n')) initNames
    newn (UN n) i = MN i n
    newn _ i = sMN i "arg"

unload :: [LExp] -> LExp -> LExp
unload [] e = e
unload stk (LApp tc e args) = LApp tc e (args ++ stk)
unload stk e = LApp False e stk

takeStk :: [(Name, LExp)] -> [Name] -> [LExp] ->
           ([(Name, LExp)], [Name], [LExp])
takeStk env (a : args) (v : stk) = takeStk ((a, v) : env) args stk
takeStk env args stk = (env, args, stk)

eval :: [LExp] -> [(Name, LExp)] -> [Name] -> LDefs -> LExp -> State Int LExp
eval stk env rec defs (LLazyApp n es)
    = unload stk <$> LLazyApp n <$> (mapM (eval [] env rec defs) es)
eval stk env rec defs (LForce e)
    = unload stk <$> LForce <$> eval [] env rec defs e
eval stk env rec defs (LLazyExp e)
    = unload stk <$> LLazyExp <$> eval [] env rec defs e
-- Special case for io_bind, because it needs to keep executing the first
-- action, and is worth inlining to avoid the thunk
eval [] env rec defs (LApp t (LV n) [_, _, _, act, (LLam [arg] k)])
    | n == sUN "io_bind"
    = do w <- nextN
         let env' = (w, LV w) : env
         act' <- eval [] env' rec defs (LApp False act [LV w])
         argn <- nextN
         k' <- eval [] ((arg, LV argn) : env') rec defs (LApp False k [LV w])
         return $ LLam [w] (LLet argn act' k')
eval (world : stk) env rec defs (LApp t (LV n) [_, _, _, act, (LLam [arg] k)])
    | n == sUN "io_bind"
    = do act' <- eval [] env rec defs (LApp False act [world])
         argn <- nextN
         k' <- eval stk ((arg, LV argn) : env) rec defs (LApp False k [world])
         return $ LLet argn act' k'

eval stk env rec defs (LApp t f es)
    = do es' <- mapM (eval [] env rec defs) es
         eval (es' ++ stk) env rec defs f
eval stk env rec defs (LLet n val sc)
    = do n' <- nextN
         LLet n' <$> eval [] env rec defs val
                 <*> eval stk ((n, LV n') : env) rec defs sc
eval stk env rec defs (LProj exp i)
    = unload stk <$> (LProj <$> eval [] env rec defs exp <*> return i)
eval stk env rec defs (LCon loc i n es)
    = unload stk <$> (LCon loc i n <$> mapM (eval [] env rec defs) es)
eval stk env rec defs (LCase ty e alts)
    = do alts' <- mapM (evalAlt stk env rec defs) alts
         e' <- eval [] env rec defs e
         -- If they're all lambdas, bind the lambda at the top
         let prefix = getLams (map getRHS alts')
         case prefix of
              [] -> return $ LCase ty e' alts'
              args -> do alts_red <- mapM (dropArgs args) alts'
                         return $ LLam args (LCase ty e' alts_red)
eval stk env rec defs (LOp f es)
    = unload stk <$> LOp f <$> mapM (eval [] env rec defs) es
eval stk env rec defs (LForeign t s args)
    = unload stk <$>
        LForeign t s <$> mapM (\(t, e) -> do e' <- eval [] env rec defs e
                                             return (t, e')) args
-- save the interesting cases for the end:
-- lambdas, and names to reduce
eval stk env rec defs (LLam args sc)
    | (env', args', stk') <- takeStk env args stk
        = case args' of
               [] -> eval stk' env' rec defs sc
               as -> do ns' <- mapM (\n -> do n' <- nextN
                                              return (n, n')) args'
                        LLam (map snd ns') <$>
                            eval [] (map (\ (n, n') -> (n, LV n')) ns' ++ env')
                                    rec defs sc
eval stk env rec defs var@(LV n)
    = case lookup n env of
           Just t
               | t /= LV n && n `notElem` rec ->
                       eval stk env (n : rec) defs t
               | otherwise -> return (unload stk t)
           Nothing
               | n `notElem` rec,
                 Just (LFun opts _ args body) <- lookupCtxtExact n defs,
                 Inline `elem` opts ->
                         apply stk env (n : rec) defs var args body
               | otherwise -> return (unload stk var)
eval stk env rec defs t = return (unload stk t)

evalAlt stk env rec defs (LConCase i n es rhs)
    = do ns' <- mapM (\n -> do n' <- nextN
                               return (n, n')) es
         LConCase i n (map snd ns') <$>
            eval stk (map (\ (n, n') -> (n, LV n')) ns' ++ env) rec defs rhs
evalAlt stk env rec defs (LConstCase c e)
    = LConstCase c <$> eval stk env rec defs e
evalAlt stk env rec defs (LDefaultCase e)
    = LDefaultCase <$> eval stk env rec defs e

dropArgs :: [Name] -> LAlt -> State Int LAlt
dropArgs as (LConCase i n es (LLam args rhs))
    = do let old = take (length as) args
         rhs' <- eval [] (zipWith (\ o n -> (o, LV n)) old as) [] emptyContext rhs
         return (LConCase i n es rhs')
dropArgs as (LConstCase c (LLam args rhs))
    = do let old = take (length as) args
         rhs' <- eval [] (zipWith (\ o n -> (o, LV n)) old as) [] emptyContext rhs
         return (LConstCase c rhs')
dropArgs as (LDefaultCase (LLam args rhs))
    = do let old = take (length as) args
         rhs' <- eval [] (zipWith (\ o n -> (o, LV n)) old as) [] emptyContext rhs
         return (LDefaultCase rhs')

-- dropArgs as (LConstCase c rhs) = LConstCase c (dropRHS as rhs)
-- dropArgs as (LDefaultCase rhs) = LDefaultCase (dropRHS as rhs)

getRHS (LConCase i n es rhs) = rhs
getRHS (LConstCase _ rhs) = rhs
getRHS (LDefaultCase rhs) = rhs

getLams [] = []
getLams (LLam args tm : cs) = getLamPrefix args cs
getLams _ = []

getLamPrefix as [] = as
getLamPrefix as (LLam args tm : cs)
    | length args < length as = getLamPrefix args cs
    | otherwise = getLamPrefix as cs
getLamPrefix as (_ : cs) = []

apply :: [LExp] -> [(Name, LExp)] -> [Name] -> LDefs -> LExp ->
         [Name] -> LExp -> State Int LExp
apply stk env rec defs var args body
    = eval stk env rec defs (LLam args body)

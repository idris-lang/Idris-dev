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
doInline = doInline' 1

doInline' :: Int -> LDefs -> LDecl -> LDecl
doInline' 0 defs d = d
doInline' i defs d@(LConstructor _ _ _) = d
doInline' i defs (LFun opts topn args exp)
      = let inl = evalState (eval [] initEnv [topn] defs exp)
                             (length args)
            -- do some case floating, which might arise as a result
            -- then, eta contract
            res = eta $ caseFloats 10 inl in
            case res of
                 LLam args' body ->
                   doInline' (i - 1) defs $
                     LFun opts topn (map snd initNames ++ args') body
                 _ -> doInline' (i - 1) defs $
                        LFun opts topn (map snd initNames) res
  where
    caseFloats 0 tm = tm
    caseFloats n tm
        = let res = caseFloat tm in
              if res == tm
                 then res
                 else caseFloats (n-1) res

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
    = do e' <- eval [] env rec defs e
         case e' of
              LLazyExp forced -> eval stk env rec defs forced
              LLazyApp n es -> eval stk env rec defs (LApp False (LV n) es)
              _ -> return (unload stk (LForce e'))
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
         -- Needs to be a LLet to make sure the action gets evaluated
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
eval stk env rec defs (LCase ty e [])
    = pure LNothing
eval stk env rec defs (LCase ty e alts)
    = do e' <- eval [] env rec defs e
         case evalAlts e' alts of
              Just (env', tm) -> eval stk env' rec defs tm
              Nothing ->
                do alts' <- mapM (evalAlt stk env rec defs) alts
                   -- If they're all lambdas, bind the lambda at the top
                   let prefix = getLams (map getRHS alts')
                   case prefix of
                        [] -> return $ LCase ty e' (replaceInAlts e' alts')
                        args -> do alts_red <- mapM (dropArgs args) alts'
                                   return $ LLam args
                                      (LCase ty e' (replaceInAlts e' alts_red))
  where
    evalAlts e' [] = Nothing
    evalAlts (LCon _ t n args) (LConCase i n' es rhs : as)
        | n == n' = Just (zip es args ++ env, rhs)
    evalAlts (LConst c) (LConstCase c' rhs : as)
        | c == c' = Just (env, rhs)
    evalAlts (LCon _ _ _ _) (LDefaultCase rhs : as) = Just (env, rhs)
    evalAlts (LConst _) (LDefaultCase rhs : as) = Just (env, rhs)
    evalAlts tm (_ : as) = evalAlts tm as
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
                            eval stk' (map (\ (n, n') -> (n, LV n')) ns' ++ env')
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
               | Just (LConstructor n t a) <- lookupCtxtExact n defs ->
                         return (LCon Nothing t n stk)
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

apply :: [LExp] -> [(Name, LExp)] -> [Name] -> LDefs -> LExp ->
         [Name] -> LExp -> State Int LExp
apply stk env rec defs var args body
    = eval stk env rec defs (LLam args body)

dropArgs :: [Name] -> LAlt -> State Int LAlt
dropArgs as (LConCase i n es t)
    = do rhs' <- dropArgsTm as t
         return (LConCase i n es rhs')
dropArgs as (LConstCase c t)
    = do rhs' <- dropArgsTm as t
         return (LConstCase c rhs')
dropArgs as (LDefaultCase t)
    = do rhs' <- dropArgsTm as t
         return (LDefaultCase rhs')

dropArgsTm as (LLam args rhs)
    = do let old = take (length as) args
         eval [] (zipWith (\ o n -> (o, LV n)) old as) [] emptyContext rhs
dropArgsTm as (LLet n val rhs)
    = do rhs' <- dropArgsTm as rhs
         pure (LLet n val rhs')
dropArgsTm as tm = return tm

caseFloat :: LExp -> LExp
caseFloat (LApp tc e es) = LApp tc (caseFloat e) (map caseFloat es)
caseFloat (LLazyExp e) = LLazyExp (caseFloat e)
caseFloat (LForce e) = LForce (caseFloat e)
caseFloat (LCon up i n es) = LCon up i n (map caseFloat es)
caseFloat (LOp f es) = LOp f (map caseFloat es)
caseFloat (LLam ns sc) = LLam ns (caseFloat sc)
caseFloat (LLet v val sc) = LLet v (caseFloat val) (caseFloat sc)
caseFloat (LCase _ (LCase ct exp alts) alts')
    | all conRHS alts || length alts == 1
    = conOpt $ replaceInCase (LCase ct (caseFloat exp) (map (updateWith alts') alts))
  where
    conRHS (LConCase _ _ _ (LCon _ _ _ _)) = True
    conRHS (LConstCase _ (LCon _ _ _ _)) = True
    conRHS (LDefaultCase (LCon _ _ _ _)) = True
    conRHS _ = False

    updateWith alts (LConCase i n es rhs) =
        LConCase i n es (caseFloat (conOpt (LCase Shared (caseFloat rhs) alts)))
    updateWith alts (LConstCase c rhs) =
        LConstCase c (caseFloat (conOpt (LCase Shared (caseFloat rhs) alts)))
    updateWith alts (LDefaultCase rhs) =
        LDefaultCase (caseFloat (conOpt (LCase Shared (caseFloat rhs) alts)))

caseFloat (LCase ct exp alts')
    = conOpt $ replaceInCase (LCase ct (caseFloat exp) (map cfAlt alts'))
  where
    cfAlt (LConCase i n es rhs) = LConCase i n es (caseFloat rhs)
    cfAlt (LConstCase c rhs) = LConstCase c (caseFloat rhs)
    cfAlt (LDefaultCase rhs) = LDefaultCase (caseFloat rhs)
caseFloat exp = exp

-- Case of constructor
conOpt :: LExp -> LExp
conOpt (LCase ct (LCon _ t n args) alts)
    = pickAlt n args alts
  where
    pickAlt n args (LConCase i n' es rhs : as) | n == n'
        = substAll (zip es args) rhs
    pickAlt _ _ (LDefaultCase rhs : as) = rhs
    pickAlt n args (_ : as) = pickAlt n args as
    pickAlt n args [] = error "Can't happen pickAlt - impossible case found"

    substAll [] rhs = rhs
    substAll ((n, tm) : ss) rhs = lsubst n tm (substAll ss rhs)
conOpt tm = tm

replaceInCase :: LExp -> LExp
replaceInCase (LCase ty e alts)
    = LCase ty e (replaceInAlts e alts)
replaceInCase exp = exp

replaceInAlts :: LExp -> [LAlt] -> [LAlt]
replaceInAlts exp alts = dropDups $ concatMap (replaceInAlt exp) alts

-- Drop overlapping case (arising from case merging of overlapping
-- patterns)
dropDups (alt@(LConCase _ i n ns) : alts)
    = alt : dropDups (filter (notTag i) alts)
  where
    notTag i (LConCase _ j n ns) = i /= j
    notTag _ _ = True
dropDups (c : alts) = c : dropDups alts
dropDups [] = []


replaceInAlt :: LExp -> LAlt -> [LAlt]
-- In an alternative, if the case appears on the right hand side, replace
-- it with the given expression, to preserve sharing
replaceInAlt exp@(LV _) (LConCase i con args rhs)
    = [LConCase i con args $
          replaceExp (LCon Nothing i con (map LV args)) exp rhs]
-- if a default case inspects the same variable as the case it's in,
-- remove the inspection and replace with the alternatives
-- (i.e. merge the inner case block)
replaceInAlt exp@(LV var) (LDefaultCase (LCase ty (LV var') alts))
    | var == var' = alts
replaceInAlt exp a = [a]

replaceExp :: LExp -> LExp -> LExp -> LExp
replaceExp (LCon _ t n args) new (LCon _ t' n' args')
    | n == n' && args == args' = new
replaceExp (LCon _ t n args) new (LApp _ (LV n') args')
    | n == n' && args == args' = new
replaceExp old new tm = tm

-- dropArgs as (LConstCase c rhs) = LConstCase c (dropRHS as rhs)
-- dropArgs as (LDefaultCase rhs) = LDefaultCase (dropRHS as rhs)

getRHS (LConCase i n es rhs) = rhs
getRHS (LConstCase _ rhs) = rhs
getRHS (LDefaultCase rhs) = rhs

getLams [] = []
getLams (LLam args tm : cs) = getLamPrefix args cs
getLams (LLet n val exp : cs) = getLams (exp : cs)
getLams _ = []

getLamPrefix as [] = as
getLamPrefix as (LLam args tm : cs)
    | length args < length as = getLamPrefix args cs
    | otherwise = getLamPrefix as cs
getLamPrefix as (LLet n val exp : cs) = getLamPrefix as (exp : cs)
getLamPrefix as (_ : cs) = []

-- eta contract ('\x -> f x' can just be compiled as 'f' when f is local)
eta :: LExp -> LExp
eta (LApp tc a es) = LApp tc (eta a) (map eta es)
eta (LLazyApp n es) = LLazyApp n (map eta es)
eta (LLazyExp e) = LLazyExp (eta e)
eta (LForce e) = LForce (eta e)
eta (LLet n val sc) = LLet n (eta val) (eta sc)
eta (LLam args (LApp tc f args'))
    | args' == map LV args = eta f
eta (LLam args e) = LLam args (eta e)
eta (LProj e i) = LProj (eta e) i
eta (LCon a t n es) = LCon a t n (map eta es)
eta (LCase ct e alts) = LCase ct (eta e) (map (fmap eta) alts)
eta (LOp f es) = LOp f (map eta es)
eta tm = tm


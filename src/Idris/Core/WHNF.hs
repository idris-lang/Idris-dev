{-|
Module      : Idris.Core.WHNF
Description : Reduction to Weak Head Normal Form
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Idris.Core.WHNF(whnf, whnfArgs, WEnv) where

import Idris.Core.CaseTree
import Idris.Core.Evaluate hiding (quote)
import qualified Idris.Core.Evaluate as Evaluate
import Idris.Core.TT

import Debug.Trace

-- | A stack entry consists of a term and the environment it is to be
-- evaluated in (i.e. it's a thunk)
type StackEntry = (Term, WEnv)

data WEnv = WEnv Int -- number of free variables
                 [(Term, WEnv)]
  deriving Show

type Stack = [StackEntry]

-- | A WHNF is a top level term evaluated in the empty environment. It is
-- always headed by either an irreducible expression, i.e. a constructor,
-- a lambda, a constant, or a postulate
--
-- Every 'Term' or 'Type' in this structure is associated with the
-- environment it was encountered in, so that when we quote back to a term
-- we get the substitutions right.

data WHNF = WDCon Int Int Bool Name (Term, WEnv) -- ^ data constructor
          | WTCon Int Int Name (Type, WEnv) -- ^ type constructor
          | WPRef Name (Term, WEnv) -- ^irreducible global (e.g. a postulate)
          | WV Int
          | WBind Name (Binder (Term, WEnv)) (Term, WEnv)
          | WApp WHNF (Term, WEnv)
          | WConstant Const
          | WProj WHNF Int
          | WType UExp
          | WUType Universe
          | WErased
          | WImpossible

-- NOTE: These aren't yet ready to be used in practice - there's still a
-- bug or two in the handling of de Bruijn indices.

-- | Reduce a term to weak head normal form.
whnf :: Context -> Env -> Term -> Term
-- whnf ctxt env tm = let res = whnf' ctxt env tm in
--                        trace (show tm ++ "\n==>\n" ++ show res ++ "\n") res
whnf ctxt env tm =
   inlineSmall ctxt env $ -- reduce small things in body. This is primarily
                          -- to get rid of any noisy "assert_smaller/assert_total"
                          -- and evaluate any simple operators, which makes things
                          -- easier to read.
     whnf' ctxt env tm
whnf' ctxt env tm =
     quote (do_whnf ctxt (map finalEntry env) (finalise tm))

-- | Reduce a type so that all arguments are expanded
whnfArgs :: Context -> Env -> Term -> Term
whnfArgs ctxt env tm = inlineSmall ctxt env $ finalise (whnfArgs' ctxt env tm)
whnfArgs' ctxt env tm
    = case whnf' ctxt env tm of
           -- The assumption is that de Bruijn indices refer to local things
           -- (so not in the external environment) so we need to instantiate
           -- the name
           Bind n b@(Pi rig _ ty _) sc ->
                    Bind n b (whnfArgs' ctxt ((n, rig, b):env)
                             (subst n (P Bound n ty) sc))
           res -> tm

finalEntry :: (Name, RigCount, Binder (TT Name)) -> (Name, RigCount, Binder (TT Name))
finalEntry (n, r, b) = (n, r, fmap finalise b)

do_whnf :: Context -> Env -> Term -> WHNF
do_whnf ctxt genv tm = eval (WEnv 0 []) [] tm
  where
    eval :: WEnv -> Stack -> Term -> WHNF
    eval wenv@(WEnv d env) stk (V i)
         | i < length env = let (tm, env') = env !! i in
                                eval env' stk tm
         | otherwise = WV i
    eval wenv@(WEnv d env) stk (Bind n (Let t v) sc)
         = eval (WEnv d ((v, wenv) : env)) stk sc
    eval (WEnv d env) ((tm, tenv) : stk) (Bind n b@(Lam _ _) sc)
         = eval (WEnv d ((tm, tenv) : env)) stk sc
    eval wenv@(WEnv d env) stk (Bind n b sc) -- stk must be empty if well typed
         =let n' = uniqueName n (map fstEnv genv) in
              WBind n' (fmap (\t -> (t, wenv)) b) (sc, WEnv (d + 1) env)

    eval env stk (P nt n ty)
         | Just (Let t v) <- lookupBinder n genv = eval env stk v
    eval env stk (P nt n ty) = apply env nt n ty stk
    eval env stk (App _ f a) = eval env ((a, env) : stk) f
    eval env stk (Constant c) = unload (WConstant c) stk

    -- Should never happen in compile time code (for now...)
    eval env stk (Proj tm i) = unload (WProj (eval env [] tm) i) stk

    eval env stk Erased = unload WErased stk
    eval env stk Impossible = unload WImpossible stk
    eval env stk (Inferred tm) = eval env stk tm
    eval env stk (TType u) = unload (WType u) stk
    eval env stk (UType u) = unload (WUType u) stk

    apply :: WEnv -> NameType -> Name -> Type -> Stack -> WHNF
    apply env nt n ty stk
          = let wp = case nt of
                          DCon t a u -> WDCon t a u n (ty, env)
                          TCon t a -> WTCon t a n (ty, env)
                          Ref -> WPRef n (ty, env)
                          _ -> WPRef n (ty, env)
                        in
            if not (tcReducible n ctxt)
               then unload wp stk
               else case lookupDefAccExact n False ctxt of
                         Just (CaseOp ci _ _ _ _ cd, acc)
                             | acc == Public || acc == Hidden ->
                          let (ns, tree) = cases_compiletime cd in
                              case evalCase env ns tree stk of
                                   Just w -> w
                                   Nothing -> unload wp stk
                         Just (Operator _ i op, acc) ->
                          if i <= length stk
                             then case runOp env op (take i stk) (drop i stk) of
                                  Just v -> v
                                  Nothing -> unload wp stk
                             else unload wp stk
                         _ -> unload wp stk

    unload :: WHNF -> Stack -> WHNF
    unload f [] = f
    unload f (a : as) = unload (WApp f a) as

    runOp :: WEnv -> ([Value] -> Maybe Value) -> Stack -> Stack -> Maybe WHNF
    runOp env op stk rest
        = do vals <- mapM tmtoValue stk
             case op vals of
                  Just (VConstant c) -> Just $ unload (WConstant c) rest
                  -- Operators run on values, so we have to convert back
                  -- and forth. This is pretty ugly, but operators that
                  -- aren't run on constants are themselves pretty ugly
                  -- (it's prim__believe_me and prim__syntacticEq, for
                  -- example) so let's not worry too much...
                  -- We will need to deal with believe_me before dropping this
                  -- into the type checker, though.
                  Just val -> Just $ eval env rest (quoteTerm val)
                  _ -> Nothing

    tmtoValue :: (Term, WEnv) -> Maybe Value
    tmtoValue (tm, tenv)
        = case eval tenv [] tm of
               WConstant c -> Just (VConstant c)
               _ -> let tm' = quoteEnv tenv tm in
                        Just (toValue ctxt [] tm')

    evalCase :: WEnv -> [Name] -> SC -> Stack -> Maybe WHNF
    evalCase wenv@(WEnv d env) ns tree args
        | length ns > length args = Nothing
        | otherwise = let args' = take (length ns) args
                          rest = drop (length ns) args in
                          do (tm, amap) <- evalTree wenv (zip ns args') tree
                             let wtm = pToVs (map fst amap) tm
                             Just $ eval (WEnv d (map snd amap)) rest wtm

    evalTree :: WEnv -> [(Name, (Term, WEnv))] -> SC ->
                Maybe (Term, [(Name, (Term, WEnv))])
    evalTree env amap (STerm tm) = Just (tm, amap)
    evalTree env amap (Case _ n alts)
        = case lookup n amap of
            Just (tm, tenv) -> findAlt env amap
                                   (deconstruct (eval tenv [] tm) []) alts
            _ -> Nothing
    evalTree _ _ _ = Nothing

    deconstruct :: WHNF -> Stack -> (WHNF, Stack)
    deconstruct (WApp f arg) stk = deconstruct f (arg : stk)
    deconstruct t stk = (t, stk)

    findAlt :: WEnv -> [(Name, (Term, WEnv))] -> (WHNF, Stack) ->
               [CaseAlt] ->
               Maybe (Term, [(Name, (Term, WEnv))])
    findAlt env amap (WDCon tag _ _ _ _, args) alts
        | Just (ns, sc) <- findTag tag alts
              = let amap' = updateAmap (zip ns args) amap in
                    evalTree env amap' sc
        | Just sc <- findDefault alts
              = evalTree env amap sc
    findAlt env amap (WConstant c, []) alts
        | Just sc <- findConst c alts
              = evalTree env amap sc
        | Just sc <- findDefault alts
              = evalTree env amap sc
    findAlt _ _ _ _ = Nothing

    findTag :: Int -> [CaseAlt] -> Maybe ([Name], SC)
    findTag i [] = Nothing
    findTag i (ConCase n j ns sc : xs) | i == j = Just (ns, sc)
    findTag i (_ : xs) = findTag i xs

    findDefault :: [CaseAlt] -> Maybe SC
    findDefault [] = Nothing
    findDefault (DefaultCase sc : xs) = Just sc
    findDefault (_ : xs) = findDefault xs

    findConst c [] = Nothing
    findConst c (ConstCase c' v : xs) | c == c' = Just v
    findConst (AType (ATInt ITNative)) (ConCase n 1 [] v : xs) = Just v
    findConst (AType ATFloat) (ConCase n 2 [] v : xs) = Just v
    findConst (AType (ATInt ITChar))  (ConCase n 3 [] v : xs) = Just v
    findConst StrType (ConCase n 4 [] v : xs) = Just v
    findConst (AType (ATInt ITBig)) (ConCase n 6 [] v : xs) = Just v
    findConst (AType (ATInt (ITFixed ity))) (ConCase n tag [] v : xs)
        | tag == 7 + fromEnum ity = Just v
    findConst c (_ : xs) = findConst c xs

    updateAmap newm amap
       = newm ++ filter (\ (x, _) -> not (elem x (map fst newm))) amap

quote :: WHNF -> Term
quote (WDCon t a u n (ty, env)) = P (DCon t a u) n (quoteEnv env ty)
quote (WTCon t a n (ty, env)) = P (TCon t a) n (quoteEnv env ty)
quote (WPRef n (ty, env)) = P Ref n (quoteEnv env ty)
quote (WV i) = V i
quote (WBind n b (sc, env)) = Bind n (fmap (\ (t, env) -> quoteEnv env t) b)
                                     (quoteEnv env sc)
quote (WApp f (a, env)) = App Complete (quote f) (quoteEnv env a)
quote (WConstant c) = Constant c
quote (WProj t i) = Proj (quote t) i
quote (WType u) = TType u
quote (WUType u) = UType u
quote WErased = Erased
quote WImpossible = Impossible

quoteEnv :: WEnv -> Term -> Term
quoteEnv (WEnv d ws) tm = qe' d ws tm
  where
    -- d is number of free variables in the external environment
    -- (all bound in the scope of 'ws')
    qe' d ts (V i)
        | (i - d) < length ts && (i - d) >= 0
              = let (tm, env) = ts !! (i - d) in
                    quoteEnv env tm
        | otherwise = V i
    qe' d ts (Bind n b sc)
        = Bind n (fmap (qe' d ts) b) (qe' (d + 1) ts sc)
    qe' d ts (App c f a)
        = App c (qe' d ts f) (qe' d ts a)
    qe' d ts (P nt n ty) = P nt n (qe' d ts ty)
    qe' d ts (Proj tm i) = Proj (qe' d ts tm) i
    qe' d ts tm = tm

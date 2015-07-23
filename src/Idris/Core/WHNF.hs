{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- Reduction to Weak Head Normal Form
module Idris.Core.WHNF(whnf, WEnv) where

import Idris.Core.TT
import Idris.Core.CaseTree
import Idris.Core.Evaluate

-- A stack entry consists of a term and the environment it is to be
-- evaluated in (i.e. it's a thunk)
type StackEntry = (Term, WEnv)
data WEnv = WEnv Int -- number of free variables
                 [(Term, WEnv)] 

type Stack = [StackEntry]

-- A WHNF is a top level term evaluated in the empty environment. It is
-- always headed by either an irreducible expression, i.e. a constructor,
-- a lambda, a constant, or a postulate

-- Every 'Term' or 'Type' in this structure is associated with the
-- environment it was encountered in, so that when we quote back to a term
-- we get the substitutions right.

data WHNF = WDCon Int Int Bool Name (Type, WEnv) -- data constructor
          | WTCon Int Int Name (Type, WEnv) -- type constructor
          | WPRef Name (Type, WEnv) -- irreducible global (e.g. a postulate)
          | WBind Name (Binder Term) (Term, WEnv)
          | WApp WHNF (Term, WEnv)
          | WConstant Const
          | WProj WHNF Int
          | WType UExp
          | WUType Universe
          | WErased
          | WImpossible

-- Reduce a *closed* term to weak head normal form.
whnf :: Context -> Term -> Term
whnf ctxt tm = quote (do_whnf ctxt (WEnv 0 []) tm)

do_whnf :: Context -> WEnv -> Term -> WHNF
do_whnf ctxt env tm = eval env [] tm
  where
    eval :: WEnv -> Stack -> Term -> WHNF
    eval wenv@(WEnv d env) stk (V i) 
         | i < length env = let (tm, env') = env !! i in
                                eval env' stk tm
         | otherwise = error "Can't happen: WHNF scope error"
    eval wenv@(WEnv d env) stk (Bind n (Let t v) sc) 
         = eval (WEnv d ((v, wenv) : env)) stk sc
    eval (WEnv d env) [] (Bind n b sc) = WBind n b (sc, WEnv (d + 1) env)
    eval (WEnv d env) ((tm, tenv) : stk) (Bind n b sc) 
         = eval (WEnv d ((tm, tenv) : env)) stk sc

    eval env stk (P nt n ty) = apply env nt n ty stk
    eval env stk (App _ f a) = eval env ((a, env) : stk) f
    eval env stk (Constant c) = unload (WConstant c) stk

    -- Should never happen in compile time code (for now...)
    eval env stk (Proj tm i) = unload (WProj (eval env [] tm) i) stk

    eval env stk Erased = unload WErased stk
    eval env stk Impossible = unload WImpossible stk
    eval env stk (TType u) = unload (WType u) stk
    eval env stk (UType u) = unload (WUType u) stk

    apply :: WEnv -> NameType -> Name -> Type -> Stack -> WHNF
    apply env nt n ty stk 
          = let wp = case nt of
                          DCon t a u -> WDCon t a u n (ty, env)
                          TCon t a -> WTCon t a n (ty, env)
                          _ -> WPRef n (ty, env)
                        in
                unload wp stk

    unload :: WHNF -> Stack -> WHNF
    unload f [] = f
    unload f (a : as) = unload (WApp f a) as

quote :: WHNF -> Term
quote (WDCon t a u n (ty, env)) = P (DCon t a u) n (quoteEnv env ty)
quote (WTCon t a n (ty, env)) = P (TCon t a) n (quoteEnv env ty)
quote (WPRef n (ty, env)) = P Ref n (quoteEnv env ty) 
quote (WBind n ty (sc, env)) = Bind n ty (quoteEnv env sc)
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
    qe' d ts (V i) 
        | i < d = V i
        | otherwise = let (tm, env) = ts !! (i - d) in
                          quoteEnv env tm
    qe' d ts (Bind n b sc)
        = Bind n (fmap (qe' d ts) b) (qe' (d + 1) ts sc)
    qe' d ts (App c f a)
        = App c (qe' d ts f) (qe' d ts a)
    qe' d ts (P nt n ty) = P nt n (qe' d ts ty)
    qe' d ts (Proj tm i) = Proj (qe' d ts tm) i
    qe' d ts tm = tm


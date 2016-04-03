{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Idris.Elab.Rewrite(elabRewrite) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Delaborate
import Idris.Error
import Idris.Core.TT
import Idris.Core.Elaborate
import Idris.Core.Evaluate

import Control.Monad
import Control.Monad.State.Strict
import Data.List

import Debug.Trace

elabRewrite :: (PTerm -> ElabD ()) -> IState -> 
               FC -> Maybe Name -> PTerm -> PTerm -> Maybe PTerm -> ElabD ()
-- Old version, no rewrite rule given
{-
elabRewrite elab ist fc Nothing rule sc newg
        = do attack
             tyn <- getNameFrom (sMN 0 "rty")
             claim tyn RType
             valn <- getNameFrom (sMN 0 "rval")
             claim valn (Var tyn)
             letn <- getNameFrom (sMN 0 "_rewrite_rule")
             letbind letn (Var tyn) (Var valn)
             focus valn
             elab rule
             compute
             g <- goal
             rewrite (Var letn)
             g' <- goal
             when (g == g') $ lift $ tfail (NoRewriting g)
             case newg of
                 Nothing -> elab sc
                 Just t -> doEquiv elab fc t sc
             solve
             -}
elabRewrite elab ist fc substfn_in rule sc_in newg
        = do attack
             sc <- case newg of
                      Nothing -> return sc_in
                      Just t -> do
                         letn <- getNameFrom (sMN 0 "rewrite_result")
                         return $ PLet fc letn fc t sc_in 
                                       (PRef fc [] letn)
             tyn <- getNameFrom (sMN 0 "rty")
             claim tyn RType
             valn <- getNameFrom (sMN 0 "rval")
             claim valn (Var tyn)
             letn <- getNameFrom (sMN 0 "_rewrite_rule")
             letbind letn (Var tyn) (Var valn)
             focus valn
             elab rule
             compute
             g <- goal
             (tmv, rule_in) <- get_type_val (Var letn)
             env <- get_env
             let ttrule = normalise (tt_ctxt ist) env rule_in
             rname <- unique_hole (sMN 0 "replaced")
             case unApply ttrule of
                  (P _ (UN q) _, [lt, rt, l, r]) | q == txt "=" ->
                     do substfn <- findSubstFn substfn_in ist lt rt
                        let pred_tt = mkP (P Bound rname rt) l r g
                        when (g == pred_tt) $ lift $ tfail (NoRewriting g)
                        let pred = PLam fc rname fc Placeholder
                                        (delab ist pred_tt)
                        let rewrite = stripImpls $
                                        addImplBound ist (map fst env) (PApp fc (PRef fc [] substfn)
                                              [pexp pred, pexp rule, pexp sc])
--                         trace ("LHS: " ++ show l ++ "\n" ++
--                                "RHS: " ++ show r ++ "\n" ++
--                                "REWRITE: " ++ show rewrite ++ "\n" ++ 
--                                "GOAL: " ++ show (delab ist g)) $
                        elab rewrite
                        solve
                  _ -> lift $ tfail (NotEquality tmv ttrule)
      where
        mkP :: TT Name -> -- Left term, top level
               TT Name -> TT Name -> TT Name -> TT Name
        mkP lt l r ty | l == ty = lt
        mkP lt l r (App s f a) 
            = let f' = if (r /= f) then mkP lt l r f else f
                  a' = if (r /= a) then mkP lt l r a else a in
                  App s f' a'
        mkP lt l r (Bind n b sc)
             = let b' = mkPB b
                   sc' = if (r /= sc) then mkP lt l r sc else sc in
                   Bind n b' sc'
            where mkPB (Let t v) = let t' = if (r /= t) then mkP lt l r t else t
                                       v' = if (r /= v) then mkP lt l r v else v in
                                       Let t' v'
                  mkPB b = let ty = binderTy b
                               ty' = if (r /= ty) then mkP lt l r ty else ty in
                                     b { binderTy = ty' }
        mkP lt l r x = x

        -- If we're rewriting a dependent type, the rewrite type the rewrite
        -- may break the indices. 
        -- So, for any function argument which can be determined by looking
        -- at the indices (i.e. any constructor guarded elsewhere in the type)
        -- replace it with a _. e.g. (++) a n m xs ys becomes (++) _ _ _ xs ys
        -- because a,n, and m are constructor guarded later in the type of ++

        -- FIXME: Currently this is an approximation which just strips
        -- implicits. This is perfectly fine for most cases, but not as
        -- general as it should be.
        stripImpls tm = mapPT phApps tm

        phApps (PApp fc f args) = PApp fc f (map removeImp args)
          where removeImp tm@(PImp{}) = tm { getTm = Placeholder }
                removeImp t = t
        phApps tm = tm
       
findSubstFn :: Maybe Name -> IState -> Type -> Type -> ElabD Name
findSubstFn Nothing ist lt rt
     | lt == rt = return (sUN "rewrite__impl")
     -- TODO: Find correct rewriting lemma, if it exists, and tidy up this
     -- error
     | otherwise = lift . tfail . 
                     Msg $ "Can't rewrite heterogeneous equality on types " ++ 
                           show (delab ist lt) ++ " and " ++ show (delab ist rt)
findSubstFn (Just substfn_in) ist lt rt
    = case lookupTyName substfn_in (tt_ctxt ist) of
           [(n, t)] -> return n
           [] -> lift . tfail . NoSuchVariable $ substfn_in
           more -> lift . tfail . CantResolveAlts $ map fst more

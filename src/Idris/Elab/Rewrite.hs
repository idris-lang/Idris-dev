{-|
Module      : Idris.Elab.Rewrite
Description : Code to elaborate rewrite rules.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Idris.Elab.Rewrite(elabRewrite, elabRewriteLemma) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Core.Elaborate
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate
import Idris.Docstrings
import Idris.Error

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
                        when (g == pred_tt) $ lift $ tfail (NoRewriting l r g)
                        let pred = PLam fc rname fc Placeholder
                                        (delab ist pred_tt)
                        let rewrite = addImplBound ist (map fstEnv env) (PApp fc (PRef fc [] substfn)
                                           [pexp (stripImpls pred),
                                            pexp (stripImpls rule), pexp sc])
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
     | (P _ lcon _, _) <- unApply lt,
       (P _ rcon _, _) <- unApply rt,
       lcon == rcon
         = case lookupTyExact (rewrite_name lcon) (tt_ctxt ist) of
                Just _ -> return (rewrite_name lcon)
                Nothing -> rewriteFail lt rt
     | otherwise = rewriteFail lt rt
  where rewriteFail lt rt = lift . tfail .
                     Msg $ "Can't rewrite heterogeneous equality on types " ++
                           show (delab ist lt) ++ " and " ++ show (delab ist rt)

findSubstFn (Just substfn_in) ist lt rt
    = case lookupTyName substfn_in (tt_ctxt ist) of
           [(n, t)] -> return n
           [] -> lift . tfail . NoSuchVariable $ substfn_in
           more -> lift . tfail . CantResolveAlts $ map fst more

rewrite_name :: Name -> Name
rewrite_name n = sMN 0 (show n ++ "_rewrite_lemma")

data ParamInfo = Index
               | Param
               | ImplicitIndex
               | ImplicitParam
  deriving Show

getParamInfo :: Type -> [PArg] -> Int -> [Int] -> [ParamInfo]
-- Skip the top level implicits, we just need the explicit ones
getParamInfo (Bind n (Pi _ _ _ _) sc) (PExp{} : is) i ps
    | i `elem` ps = Param : getParamInfo sc is (i + 1) ps
    | otherwise = Index : getParamInfo sc is (i + 1) ps
getParamInfo (Bind n (Pi _ _ _ _) sc) (_ : is) i ps
    | i `elem` ps = ImplicitParam : getParamInfo sc is (i + 1) ps
    | otherwise = ImplicitIndex : getParamInfo sc is (i + 1) ps
getParamInfo _ _ _ _ = []

isParam Index = False
isParam Param = True
isParam ImplicitIndex = False
isParam ImplicitParam = True

-- | Make a rewriting lemma for the given type constructor.
--
-- If it fails, fail silently (it may well fail for some very complex
-- types.  We can fix this later, for now this gives us a lot more
-- working rewrites...)
elabRewriteLemma :: ElabInfo -> Name -> Type -> Idris ()
elabRewriteLemma info n cty_in =
    do ist <- getIState
       let cty = normalise (tt_ctxt ist) [] cty_in
       let rewrite_lem = rewrite_name n
       case lookupCtxtExact n (idris_datatypes ist) of
            Nothing -> fail $ "Can't happen, elabRewriteLemma for " ++ show n
            Just ti -> do
               let imps = case lookupCtxtExact n (idris_implicits ist) of
                               Nothing -> repeat (pexp Placeholder)
                               Just is -> is
               let pinfo = getParamInfo cty imps 0 (param_pos ti)
               if all isParam pinfo
                  then return () -- no need for a lemma, = will be homogeneous
                  else idrisCatch (mkLemma info rewrite_lem n pinfo cty)
                                  (\_ -> return ())

mkLemma :: ElabInfo -> Name -> Name -> [ParamInfo] -> Type -> Idris ()
mkLemma info lemma tcon ps ty =
    do ist <- getIState
       let leftty = mkTy tcon ps (namesFrom "p" 0) (namesFrom "left" 0)
           rightty = mkTy tcon ps (namesFrom "p" 0) (namesFrom "right" 0)
           predty = bindIdxs ist ps ty (namesFrom "pred" 0) $
                        PPi expl (sMN 0 "rep") fc
                          (mkTy tcon ps (namesFrom "p" 0) (namesFrom "pred" 0))
                          (PType fc)
       let xarg = sMN 0 "x"
       let yarg = sMN 0 "y"
       let parg = sMN 0 "P"
       let eq = sMN 0 "eq"
       let prop = sMN 0 "prop"
       let lemTy = PPi impl xarg fc leftty $
                   PPi impl yarg fc rightty $
                   PPi expl parg fc predty $
                   PPi expl eq fc (PApp fc (PRef fc [] (sUN "="))
                                       [pexp (PRef fc [] xarg),
                                        pexp (PRef fc [] yarg)]) $
                   PPi expl prop fc (PApp fc (PRef fc [] parg)
                                       [pexp (PRef fc [] yarg)]) $
                       PApp fc (PRef fc [] parg) [pexp (PRef fc [] xarg)]

       let lemLHS = PApp fc (PRef fc [] lemma)
                            [pexp (PRef fc [] parg),
                             pexp (PRef fc [] (sUN "Refl")),
                             pexp (PRef fc [] prop)]

       let lemRHS = PRef fc [] prop

       -- Elaborate the type of the lemma
       rec_elabDecl info EAll info
            (PTy emptyDocstring [] defaultSyntax fc [] lemma fc lemTy)
       -- Elaborate the definition
       rec_elabDecl info EAll info
            (PClauses fc [] lemma [PClause fc lemma lemLHS [] lemRHS []])

  where
    fc = emptyFC

    namesFrom x i = sMN i (x ++ show i) : namesFrom x (i + 1)

    mkTy fn pinfo ps is
         = PApp fc (PRef fc [] fn) (mkArgs pinfo ps is)

    mkArgs [] ps is = []
    mkArgs (Param : pinfo) (p : ps) is
         = pexp (PRef fc [] p) : mkArgs pinfo ps is
    mkArgs (Index : pinfo) ps (i : is)
         = pexp (PRef fc [] i) : mkArgs pinfo ps is
    mkArgs (ImplicitParam : pinfo) (p : ps) is
         = mkArgs pinfo ps is
    mkArgs (ImplicitIndex : pinfo) ps (i : is)
         = mkArgs pinfo ps is
    mkArgs _ _ _ = []

    bindIdxs ist [] ty is tm = tm
    bindIdxs ist (Param : pinfo) (Bind n (Pi _ _ ty _) sc) is tm
         = bindIdxs ist pinfo (instantiate (P Bound n ty) sc) is tm
    bindIdxs ist (Index : pinfo) (Bind n (Pi _ _ ty _) sc) (i : is) tm
        = PPi forall_imp i fc (delab ist ty)
               (bindIdxs ist pinfo (instantiate (P Bound n ty) sc) is tm)
    bindIdxs ist (ImplicitParam : pinfo) (Bind n (Pi _ _ ty _) sc) is tm
        = bindIdxs ist pinfo (instantiate (P Bound n ty) sc) is tm
    bindIdxs ist (ImplicitIndex : pinfo) (Bind n (Pi _ _ ty _) sc) (i : is) tm
        = bindIdxs ist pinfo (instantiate (P Bound n ty) sc) is tm
    bindIdxs _ _ _ _ tm = tm

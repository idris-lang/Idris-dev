{-|
Module      : Idris.Core.Evaluate
Description : Evaluate Idris expressions.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE BangPatterns, DeriveGeneric, FlexibleInstances,
             MultiParamTypeClasses, PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Idris.Core.Evaluate(normalise, normaliseTrace, normaliseC,
                normaliseAll, normaliseBlocking, toValue, quoteTerm,
                rt_simplify, simplify, inlineSmall,
                specialise, unfold, convEq, convEq',
                Def(..), CaseInfo(..), CaseDefs(..),
                Accessibility(..), Injectivity, Totality(..), TTDecl, PReason(..), MetaInformation(..),
                Context, initContext, ctxtAlist, next_tvar,
                addToCtxt, setAccess, setInjective, setTotal, setRigCount,
                setMetaInformation, addCtxtDef, addTyDecl,
                addDatatype, addCasedef, simplifyCasedef, addOperator,
                lookupNames, lookupTyName, lookupTyNameExact, lookupTy, lookupTyExact,
                lookupP, lookupP_all, lookupDef, lookupNameDef, lookupDefExact, lookupDefAcc, lookupDefAccExact, lookupVal,
                mapDefCtxt, tcReducible,
                lookupTotal, lookupTotalExact, lookupInjectiveExact,
                lookupRigCount, lookupRigCountExact,
                lookupNameTotal, lookupMetaInformation, lookupTyEnv, isTCDict,
                isCanonical, isDConName, canBeDConName, isTConName, isConName, isFnName,
                conGuarded,
                Value(..), Quote(..), initEval, uniqueNameCtxt, uniqueBindersCtxt, definitions,
                isUniverse, linearCheck, linearCheckArg) where

import Idris.Core.CaseTree
import Idris.Core.TT

import Control.Applicative hiding (Const)
import Control.Monad.State
import Data.Binary hiding (get, put)
import qualified Data.Binary as B
import Data.List
import Data.Maybe (listToMaybe)
import Debug.Trace
import GHC.Generics (Generic)

data EvalState = ES { limited :: [(Name, Int)],
                      nexthole :: Int,
                      blocking :: Bool }
  deriving Show

type Eval a = State EvalState a

data EvalOpt = Spec
             | Simplify Bool -- ^ whether to expand lets or not
             | AtREPL
             | RunTT
             | Unfold
  deriving (Show, Eq)

initEval = ES [] 0 False

-- VALUES (as HOAS) ---------------------------------------------------------
-- | A HOAS representation of values
data Value = VP NameType Name Value
           | VV Int
             -- True for Bool indicates safe to reduce
           | VBind Bool Name (Binder Value) (Value -> Eval Value)
             -- For frozen let bindings when simplifying
           | VBLet Int Name Value Value Value
           | VApp Value Value
           | VType UExp
           | VUType Universe
           | VErased
           | VImpossible
           | VConstant Const
           | VProj Value Int
--            | VLazy Env [Value] Term
           | VTmp Int

canonical :: Value -> Bool
canonical (VP (DCon _ _ _) _ _) = True
canonical (VApp f a) = canonical f
canonical (VConstant _) = True
canonical (VType _) = True
canonical (VUType _) = True
canonical VErased = True
canonical _ = False


instance Show Value where
    show x = show $ evalState (quote 100 x) initEval

instance Show (a -> b) where
    show x = "<<fn>>"

-- THE EVALUATOR ------------------------------------------------------------

-- The environment is assumed to be "locally named" - i.e., not de Bruijn
-- indexed.
-- i.e. it's an intermediate environment that we have while type checking or
-- while building a proof.

-- | Normalise fully type checked terms (so, assume all names/let bindings resolved)
normaliseC :: Context -> Env -> TT Name -> TT Name
normaliseC ctxt env t
   = evalState (do val <- eval False ctxt [] (map finalEntry env) t []
                   quote 0 val) initEval

-- | Normalise everything, whether abstract, private or public
normaliseAll :: Context -> Env -> TT Name -> TT Name
normaliseAll ctxt env t
   = evalState (do val <- eval False ctxt [] (map finalEntry env) t [AtREPL]
                   quote 0 val) initEval

-- | As normaliseAll, but with an explicit list of names *not* to reduce
normaliseBlocking :: Context -> Env -> [Name] -> TT Name -> TT Name
normaliseBlocking ctxt env blocked t
   = evalState (do val <- eval False ctxt (map (\n -> (n, 0)) blocked)
                                          (map finalEntry env) t [AtREPL]
                   quote 0 val) initEval

normalise :: Context -> Env -> TT Name -> TT Name
normalise = normaliseTrace False

normaliseTrace :: Bool -> Context -> Env -> TT Name -> TT Name
normaliseTrace tr ctxt env t
   = evalState (do val <- eval tr ctxt [] (map finalEntry env) (finalise t) []
                   quote 0 val) initEval

toValue :: Context -> Env -> TT Name -> Value
toValue ctxt env t
  = evalState (eval False ctxt [] (map finalEntry env) t []) initEval

quoteTerm :: Value -> TT Name
quoteTerm val = evalState (quote 0 val) initEval

-- Return a specialised name, and an updated list of reductions available,
-- so that the caller can tell how much specialisation was achieved.
specialise :: Context -> Env -> [(Name, Int)] -> TT Name ->
              (TT Name, [(Name, Int)])
specialise ctxt env limits t
   = let (tm, st) =
          runState (do val <- eval False ctxt []
                                 (map finalEntry env) (finalise t)
                                 [Spec]
                       quote 0 val) (initEval { limited = limits }) in
         (tm, limited st)

-- | Like normalise, but we only reduce functions that are marked as okay to
-- inline, and lets
simplify :: Context -> Env -> TT Name -> TT Name
simplify ctxt env t
   = evalState (do val <- eval False ctxt [(sUN "lazy", 0),
                                           (sUN "force", 0),
                                           (sUN "Force", 0),
                                           (sUN "assert_smaller", 0),
                                           (sUN "assert_total", 0),
                                           (sUN "par", 0),
                                           (sUN "prim__syntactic_eq", 0),
                                           (sUN "fork", 0)]
                                 (map finalEntry env) (finalise t)
                                 [Simplify True]
                   quote 0 val) initEval

-- | Like simplify, but we only reduce functions that are marked as okay to
-- inline, and don't reduce lets
inlineSmall :: Context -> Env -> TT Name -> TT Name
inlineSmall ctxt env t
   = evalState (do val <- eval False ctxt []
                                 (map finalEntry env) (finalise t)
                                 [Simplify False]
                   quote 0 val) initEval

-- | Simplify for run-time (i.e. basic inlining)
rt_simplify :: Context -> Env -> TT Name -> TT Name
rt_simplify ctxt env t
   = evalState (do val <- eval False ctxt [(sUN "lazy", 0),
                                           (sUN "force", 0),
                                           (sUN "Force", 0),
                                           (sUN "par", 0),
                                           (sUN "prim__syntactic_eq", 0),
                                           (sUN "prim_fork", 0)]
                                 (map finalEntry env) (finalise t)
                                 [RunTT]
                   quote 0 val) initEval

-- | Unfold the given names in a term, the given number of times in a stack.
-- Preserves 'let'.
-- This is primarily to support inlining of the given names, and can also
-- help with partial evaluation by allowing a rescursive definition to be
-- unfolded once only.
-- Specifically used to unfold definitions using interfaces before going to
-- the totality checker (otherwise mutually recursive definitions in
-- implementations will not work...)
unfold :: Context -> Env -> [(Name, Int)] -> TT Name -> TT Name
unfold ctxt env ns t
   = evalState (do val <- eval False ctxt ns
                               (map finalEntry env) (finalise t)
                               [Unfold]
                   quote 0 val) initEval


-- unbindEnv env (quote 0 (eval ctxt (bindEnv env t)))

finalEntry :: (Name, RigCount, Binder (TT Name)) -> (Name, RigCount, Binder (TT Name))
finalEntry (n, r, b) = (n, r, fmap finalise b)

bindEnv :: EnvTT n -> TT n -> TT n
bindEnv [] tm = tm
bindEnv ((n, r, Let t v):bs) tm = Bind n (NLet t v) (bindEnv bs tm)
bindEnv ((n, r, b):bs)       tm = Bind n b (bindEnv bs tm)

unbindEnv :: EnvTT n -> TT n -> TT n
unbindEnv [] tm = tm
unbindEnv (_:bs) (Bind n b sc) = unbindEnv bs sc
unbindEnv env tm = error "Impossible case occurred: couldn't unbind env."

usable :: Bool -- specialising
          -> Bool -- unfolding only
          -> Int -- Reduction depth limit (when simplifying/at REPL)
          -> Name -> [(Name, Int)] -> Eval (Bool, [(Name, Int)])
-- usable _ _ ns@((MN 0 "STOP", _) : _) = return (False, ns)
usable False uf depthlimit n [] = return (True, [])
usable True uf depthlimit n ns
  = do ES ls num b <- get
       if b then return (False, ns)
            else case lookup n ls of
                    Just 0 -> return (False, ns)
                    Just i -> return (True, ns)
                    _ -> return (False, ns)
usable False uf depthlimit n ns
  = case lookup n ns of
         Just 0 -> return (False, ns)
         Just i -> return $ (True, (n, abs (i-1)) : filter (\ (n', _) -> n/=n') ns)
         _ -> return $ if uf
                          then (False, ns)
                          else (True, (n, depthlimit) : filter (\ (n', _) -> n/=n') ns)


fnCount :: Int -> Name -> Eval ()
fnCount inc n
         = do ES ls num b <- get
              case lookup n ls of
                  Just i -> do put $ ES ((n, (i - inc)) :
                                           filter (\ (n', _) -> n/=n') ls) num b
                  _ -> return ()

setBlock :: Bool -> Eval ()
setBlock b = do ES ls num _ <- get
                put (ES ls num b)

deduct = fnCount 1
reinstate = fnCount (-1)

-- | Evaluate in a context of locally named things (i.e. not de Bruijn indexed,
-- such as we might have during construction of a proof)

-- The (Name, Int) pair in the arguments is the maximum depth of unfolding of
-- a name. The corresponding pair in the state is the maximum number of
-- unfoldings overall.

eval :: Bool -> Context -> [(Name, Int)] -> Env -> TT Name ->
        [EvalOpt] -> Eval Value
eval traceon ctxt ntimes genv tm opts = ev ntimes [] True [] tm where
    spec = Spec `elem` opts
    simpl = Simplify True `elem` opts || Simplify False `elem` opts
    simpl_inline = Simplify False `elem` opts
    runtime = RunTT `elem` opts
    atRepl = AtREPL `elem` opts
    unfold = Unfold `elem` opts

    noFree = all canonical . map snd

    -- returns 'True' if the function should block
    -- normal evaluation should return false
    blockSimplify (CaseInfo inl always dict) n stk
       | runtime
           = if always then False
                       else not (inl || dict) || elem n stk
       | simpl
           = (not inl || elem n stk)
             || (n == sUN "prim__syntactic_eq")
       | otherwise = False

    getCases cd | simpl = cases_compiletime cd
                | runtime = cases_runtime cd
                | otherwise = cases_compiletime cd

    ev ntimes stk top env (P _ n ty)
        | Just (Let t v) <- lookupBinder n genv = ev ntimes stk top env v
    ev ntimes_in stk top env (P Ref n ty)
         = do let limit = if simpl then 100 else 10000
              (u, ntimes) <- usable spec unfold limit n ntimes_in
              let red = u && (tcReducible n ctxt || spec || (atRepl && noFree env)
                                || runtime || unfold
                                || sUN "assert_total" `elem` stk)
              if red then
               do let val = lookupDefAccExact n (spec || unfold || (atRepl && noFree env) || runtime) ctxt
                  case val of
                    Just (Function _ tm, Public) ->
                           ev ntimes (n:stk) True env tm
                    Just (TyDecl nt ty, _) -> do vty <- ev ntimes stk True env ty
                                                 return $ VP nt n vty
                    Just (CaseOp ci _ _ _ _ cd, acc)
                         | (acc == Public || acc == Hidden) &&
--                                || sUN "assert_total" `elem` stk) &&
                             null (fst (cases_compiletime cd)) -> -- unoptimised version
                       let (ns, tree) = getCases cd in
                         if blockSimplify ci n stk
                            then liftM (VP Ref n) (ev ntimes stk top env ty)
                            else -- traceWhen runtime (show (n, ns, tree)) $
                                 do c <- evCase ntimes n (n:stk) top env ns [] tree
                                    case c of
                                        (Nothing, _) -> liftM (VP Ref n) (ev ntimes stk top env ty)
                                        (Just v, _)  -> return v
                    _ -> liftM (VP Ref n) (ev ntimes stk top env ty)
               else liftM (VP Ref n) (ev ntimes stk top env ty)
    ev ntimes stk top env (P nt n ty)
        = liftM (VP nt n) (ev ntimes stk top env ty)
    ev ntimes stk top env (V i)
        | i < length env && i >= 0 = return $ snd (env !! i)
        | otherwise      = return $ VV i
    ev ntimes stk top env (Bind n (Let t v) sc)
        | (not (runtime || simpl_inline || unfold)) || occurrences n sc < 2
           = do v' <- ev ntimes stk top env v --(finalise v)
                sc' <- ev ntimes stk top ((n, v') : env) sc
                wknV (-1) sc'
        | otherwise
           = do t' <- ev ntimes stk top env t
                v' <- ev ntimes stk top env v --(finalise v)
                -- use Tmp as a placeholder, then make it a variable reference
                -- again when evaluation finished
                hs <- get
                let vd = nexthole hs
                put (hs { nexthole = vd + 1 })
                sc' <- ev ntimes stk top ((n, VP Bound (sMN vd "vlet") VErased) : env) sc
                return $ VBLet vd n t' v' sc'
    ev ntimes stk top env (Bind n (NLet t v) sc)
           = do t' <- ev ntimes stk top env (finalise t)
                v' <- ev ntimes stk top env (finalise v)
                sc' <- ev ntimes stk top ((n, v') : env) sc
                return $ VBind True n (Let t' v') (\x -> return sc')
    ev ntimes stk top env (Bind n b sc)
           = do b' <- vbind env b
                let n' = uniqueName n (map fstEnv genv ++ map fst env)
                return $ VBind True -- (vinstances 0 sc < 2)
                               n' b' (\x -> ev ntimes stk False ((n', x):env) sc)
       where vbind env t
                     = fmapMB (\tm -> ev ntimes stk top env (finalise tm)) t
    -- block reduction immediately under codata (and not forced)
    ev ntimes stk top env
              (App _ (App _ (App _ d@(P _ (UN dly) _) l@(P _ (UN lco) _)) t) arg)
       | dly == txt "Delay" && lco == txt "Infinite" && not (unfold || simpl)
            = do let (f, _) = unApply arg
                 let ntimes' = case f of
                                    P _ fn _ -> (fn, 0) : ntimes
                                    _ -> ntimes
                 when spec $ setBlock True
                 d' <- ev ntimes' stk False env d
                 l' <- ev ntimes' stk False env l
                 t' <- ev ntimes' stk False env t
                 arg' <- ev ntimes' stk False env arg
                 when spec $ setBlock False
                 evApply ntimes' stk top env [l',t',arg'] d'
    -- Treat "assert_total" specially, as long as it's defined!
    ev ntimes stk top env (App _ (App _ (P _ n@(UN at) _) _) arg)
       | Just (CaseOp _ _ _ _ _ _, _) <- lookupDefAccExact n (spec || (atRepl && noFree env)|| runtime) ctxt,
         at == txt "assert_total" && not (simpl || unfold)
            = ev ntimes (n : stk) top env arg
    ev ntimes stk top env (App _ f a)
           = do f' <- ev ntimes stk False env f
                a' <- ev ntimes stk False env a
                evApply ntimes stk top env [a'] f'
    ev ntimes stk top env (Proj t i)
           = do -- evaluate dictionaries if it means the projection works
                t' <- ev ntimes stk top env t
--                 tfull' <- reapply ntimes stk top env t' []
                return (doProj t' (getValArgs t'))
       where doProj t' (VP (DCon _ _ _) _ _, args)
                  | i >= 0 && i < length args = args!!i
             doProj t' _ = VProj t' i

    ev ntimes stk top env (Constant c) = return $ VConstant c
    ev ntimes stk top env Erased    = return VErased
    ev ntimes stk top env Impossible  = return VImpossible
    ev ntimes stk top env (Inferred tm) = ev ntimes stk top env tm
    ev ntimes stk top env (TType i)   = return $ VType i
    ev ntimes stk top env (UType u)   = return $ VUType u

    evApply ntimes stk top env args (VApp f a)
          = evApply ntimes stk top env (a:args) f
    evApply ntimes stk top env args f
          = apply ntimes stk top env f args

    reapply ntimes stk top env f@(VP Ref n ty) args
       = let val = lookupDefAccExact n (spec || (atRepl && noFree env) || runtime) ctxt in
         case val of
              Just (CaseOp ci _ _ _ _ cd, acc) ->
                 let (ns, tree) = getCases cd in
                     do c <- evCase ntimes n (n:stk) top env ns args tree
                        case c of
                             (Nothing, _) -> return $ unload env (VP Ref n ty) args
                             (Just v, rest) -> evApply ntimes stk top env rest v
              _ -> case args of
                        (a : as) -> return $ unload env f (a : as)
                        [] -> return f
    reapply ntimes stk top env (VApp f a) args
            = reapply ntimes stk top env f (a : args)
    reapply ntimes stk top env v args = return v

    apply ntimes stk top env (VBind True n (Lam _ t) sc) (a:as)
         = do a' <- sc a
              app <- apply ntimes stk top env a' as
              wknV 1 app
    apply ntimes_in stk top env f@(VP Ref n ty) args
         = do let limit = if simpl then 100 else 10000
              (u, ntimes) <- usable spec unfold limit n ntimes_in
              let red = u && (tcReducible n ctxt || spec || (atRepl && noFree env)
                                || unfold || runtime
                                || sUN "assert_total" `elem` stk)
              if red then
                 do let val = lookupDefAccExact n (spec || unfold || (atRepl && noFree env) || runtime) ctxt
                    case val of
                      Just (CaseOp ci _ _ _ _ cd, acc)
                           | acc == Public || acc == Hidden ->
                           -- unoptimised version
                       let (ns, tree) = getCases cd in
                         if blockSimplify ci n stk
                           then return $ unload env (VP Ref n ty) args
                           else -- traceWhen runtime (show (n, ns, tree)) $
                                do c <- evCase ntimes n (n:stk) top env ns args tree
                                   case c of
                                      (Nothing, _) -> return $ unload env (VP Ref n ty) args
                                      (Just v, rest) -> evApply ntimes stk top env rest v
                      Just (Operator _ i op, _)  ->
                        if (i <= length args)
                           then case op (take i args) of
                              Nothing -> return $ unload env (VP Ref n ty) args
                              Just v  -> evApply ntimes stk top env (drop i args) v
                           else return $ unload env (VP Ref n ty) args
                      _ -> case args of
                              [] -> return f
                              _ -> return $ unload env f args
                 else case args of
                           (a : as) -> return $ unload env f (a:as)
                           [] -> return f
    apply ntimes stk top env f (a:as) = return $ unload env f (a:as)
    apply ntimes stk top env f []     = return f

--     specApply stk env f@(VP Ref n ty) args
--         = case lookupCtxt n statics of
--                 [as] -> if or as
--                           then trace (show (n, map fst (filter (\ (_, s) -> s) (zip args as)))) $
--                                 return $ unload env f args
--                           else return $ unload env f args
--                 _ -> return $ unload env f args
--     specApply stk env f args = return $ unload env f args

    unload :: [(Name, Value)] -> Value -> [Value] -> Value
    unload env f [] = f
    unload env f (a:as) = unload env (VApp f a) as

    evCase ntimes n stk top env ns args tree
        | length ns <= length args
             = do let args' = take (length ns) args
                  let rest  = drop (length ns) args
                  when spec $ deduct n
                  t <- evTree ntimes stk top env (zip ns args') tree
                  when spec $ case t of
                                   Nothing -> reinstate n -- Blocked, count n again
                                   Just _ -> return ()
--                                 (zipWith (\n , t) -> (n, t)) ns args') tree
                  return (t, rest)
        | otherwise = return (Nothing, args)

    evTree :: [(Name, Int)] -> [Name] -> Bool ->
              [(Name, Value)] -> [(Name, Value)] -> SC -> Eval (Maybe Value)
    evTree ntimes stk top env amap (UnmatchedCase str) = return Nothing
    evTree ntimes stk top env amap (STerm tm)
        = do let etm = pToVs (map fst amap) tm
             etm' <- ev ntimes stk (not (conHeaded tm))
                                   (amap ++ env) etm
             return $ Just etm'
    evTree ntimes stk top env amap (ProjCase t alts)
        = do t' <- ev ntimes stk top env t
             doCase ntimes stk top env amap t' alts
    evTree ntimes stk top env amap (Case _ n alts)
        = case lookup n amap of
            Just v -> doCase ntimes stk top env amap v alts
            _ -> return Nothing
    evTree ntimes stk top env amap ImpossibleCase = return Nothing

    doCase ntimes stk top env amap v alts =
            do c <- chooseAlt env v (getValArgs v) alts amap
               case c of
                    Just (altmap, sc) -> evTree ntimes stk top env altmap sc
                    _ -> do c' <- chooseAlt' ntimes stk env v (getValArgs v) alts amap
                            case c' of
                                 Just (altmap, sc) -> evTree ntimes stk top env altmap sc
                                 _ -> return Nothing

    conHeaded tm@(App _ _ _)
        | (P (DCon _ _ _) _ _, args) <- unApply tm = True
    conHeaded t = False

    chooseAlt' ntimes  stk env _ (f, args) alts amap
        = do f' <- apply ntimes stk True env f args
             chooseAlt env f' (getValArgs f')
                       alts amap

    chooseAlt :: [(Name, Value)] -> Value -> (Value, [Value]) -> [CaseAlt] ->
                 [(Name, Value)] ->
                 Eval (Maybe ([(Name, Value)], SC))
    chooseAlt env _ (VP (DCon i a _) _ _, args) alts amap
        | Just (ns, sc) <- findTag i alts = return $ Just (updateAmap (zip ns args) amap, sc)
        | Just v <- findDefault alts      = return $ Just (amap, v)
    chooseAlt env _ (VP (TCon i a) _ _, args) alts amap
        | Just (ns, sc) <- findTag i alts
                            = return $ Just (updateAmap (zip ns args) amap, sc)
        | Just v <- findDefault alts      = return $ Just (amap, v)
    chooseAlt env _ (VConstant c, []) alts amap
        | Just v <- findConst c alts      = return $ Just (amap, v)
        | Just (n', sub, sc) <- findSuc c alts
                            = return $ Just (updateAmap [(n',sub)] amap, sc)
        | Just v <- findDefault alts      = return $ Just (amap, v)
    chooseAlt env _ (VP _ n _, args) alts amap
        | Just (ns, sc) <- findFn n alts  = return $ Just (updateAmap (zip ns args) amap, sc)
    chooseAlt env _ (VBind _ _ (Pi _ i s k) t, []) alts amap
        | Just (ns, sc) <- findFn (sUN "->") alts
           = do t' <- t (VV 0) -- we know it's not in scope or it's not a pattern
                return $ Just (updateAmap (zip ns [s, t']) amap, sc)
    chooseAlt _ _ _ alts amap
        | Just v <- findDefault alts
             = if (any fnCase alts)
                  then return $ Just (amap, v)
                  else return Nothing
        | otherwise = return Nothing

    fnCase (FnCase _ _ _) = True
    fnCase _ = False

    -- Replace old variable names in the map with new matches
    -- (This is possibly unnecessary since we make unique names and don't
    -- allow repeated variables...?)
    updateAmap newm amap
       = newm ++ filter (\ (x, _) -> not (elem x (map fst newm))) amap
    findTag i [] = Nothing
    findTag i (ConCase n j ns sc : xs) | i == j = Just (ns, sc)
    findTag i (_ : xs) = findTag i xs

    findFn fn [] = Nothing
    findFn fn (FnCase n ns sc : xs) | fn == n = Just (ns, sc)
    findFn fn (_ : xs) = findFn fn xs

    findDefault [] = Nothing
    findDefault (DefaultCase sc : xs) = Just sc
    findDefault (_ : xs) = findDefault xs

    findSuc c [] = Nothing
    findSuc (BI val) (SucCase n sc : _)
         | val /= 0 = Just (n, VConstant (BI (val - 1)), sc)
    findSuc c (_ : xs) = findSuc c xs

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

    getValArgs tm = getValArgs' tm []
    getValArgs' (VApp f a) as = getValArgs' f (a:as)
    getValArgs' f as = (f, as)

-- tmpToV i vd (VLetHole j) | vd == j = return $ VV i
-- tmpToV i vd (VP nt n v) = liftM (VP nt n) (tmpToV i vd v)
-- tmpToV i vd (VBind n b sc) = do b' <- fmapMB (tmpToV i vd) b
--                                 let sc' = \x -> do x' <- sc x
--                                                    tmpToV (i + 1) vd x'
--                                 return (VBind n b' sc')
-- tmpToV i vd (VApp f a) = liftM2 VApp (tmpToV i vd f) (tmpToV i vd a)
-- tmpToV i vd x = return x

instance Eq Value where
    (==) x y = getTT x == getTT y
      where getTT v = evalState (quote 0 v) initEval

class Quote a where
    quote :: Int -> a -> Eval (TT Name)

instance Quote Value where
    quote i (VP nt n v)      = liftM (P nt n) (quote i v)
    quote i (VV x)           = return $ V x
    quote i (VBind _ n b sc) = do sc' <- sc (VTmp i)
                                  b' <- quoteB b
                                  liftM (Bind n b') (quote (i+1) sc')
       where quoteB t = fmapMB (quote i) t
    quote i (VBLet vd n t v sc)
                           = do sc' <- quote i sc
                                t' <- quote i t
                                v' <- quote i v
                                let sc'' = pToV (sMN vd "vlet") (addBinder sc')
                                return (Bind n (Let t' v') sc'')
    quote i (VApp f a)     = liftM2 (App MaybeHoles) (quote i f) (quote i a)
    quote i (VType u)      = return (TType u)
    quote i (VUType u)     = return (UType u)
    quote i VErased        = return Erased
    quote i VImpossible    = return Impossible
    quote i (VProj v j)    = do v' <- quote i v
                                return (Proj v' j)
    quote i (VConstant c)  = return $ Constant c
    quote i (VTmp x)       = return $ V (i - x - 1)

wknV :: Int -> Value -> Eval Value
wknV i (VV x) | x >= i = return $ VV (x - 1)
wknV i (VBind red n b sc) = do b' <- fmapMB (wknV i) b
                               return $ VBind red n b' (\x -> do x' <- sc x
                                                                 wknV (i + 1) x')
wknV i (VApp f a)     = liftM2 VApp (wknV i f) (wknV i a)
wknV i t              = return t

isUniverse :: Term -> Bool
isUniverse (TType _) = True
isUniverse (UType _) = True
isUniverse _ = False

isUsableUniverse :: Term -> Bool
isUsableUniverse (UType NullType) = False
isUsableUniverse x = isUniverse x

convEq' ctxt hs x y = evalStateT (convEq ctxt hs x y) (0, [])

convEq :: Context -> [Name] -> TT Name -> TT Name -> StateT UCs TC Bool
convEq ctxt holes topx topy = ceq [] topx topy where
    ceq :: [(Name, Name)] -> TT Name -> TT Name -> StateT UCs TC Bool
    ceq ps (P xt x _) (P yt y _)
        | x `elem` holes || y `elem` holes = return True
        | x == y || (x, y) `elem` ps || (y,x) `elem` ps = return True
        | otherwise = sameDefs ps x y

    ceq ps (Bind n (PVar _ t) sc) y = ceq ps sc y
    ceq ps x (Bind n (PVar _ t) sc) = ceq ps x sc
    ceq ps (Bind n (PVTy t) sc) y = ceq ps sc y
    ceq ps x (Bind n (PVTy t) sc) = ceq ps x sc

    ceq ps (V x)      (V y)      = return (x == y)
    ceq ps (V x)      (P _ y _)
        | x >= 0 && length ps > x = return (fst (ps!!x) == y)
        | otherwise = return False
    ceq ps (P _ x _)  (V y)
        | y >= 0 && length ps > y = return (x == snd (ps!!y))
        | otherwise = return False
    ceq ps (Bind n xb xs) (Bind n' yb ys)
                             = liftM2 (&&) (ceqB ps xb yb) (ceq ((n,n'):ps) xs ys)
        where
            ceqB ps (Let v t) (Let v' t') = liftM2 (&&) (ceq ps v v') (ceq ps t t')
            ceqB ps (Guess v t) (Guess v' t') = liftM2 (&&) (ceq ps v v') (ceq ps t t')
            ceqB ps (Pi r i v t) (Pi r' i' v' t') = liftM2 (&&) (ceq ps v v') (ceq ps t t')
            ceqB ps b b' = ceq ps (binderTy b) (binderTy b')

    ceq ps x (Bind n (Lam _ t) (App _ y (V 0)))
          = ceq ps x (substV (P Bound n t) y)
    ceq ps (Bind n (Lam _ t) (App _ x (V 0))) y
          = ceq ps (substV (P Bound n t) x) y
    ceq ps x (Bind n (Lam _ t) (App _ y (P Bound n' _)))
        | n == n' = ceq ps x y
    ceq ps (Bind n (Lam _ t) (App _ x (P Bound n' _))) y
        | n == n' = ceq ps x y

    -- Special case for 'case' blocks - size of scope causes complications,
    -- we only want to check the blocks themselves are valid and identical
    -- in the current scope. So, just check the bodies, and the additional
    -- arguments the case blocks are applied to.
    ceq ps x@(App _ _ _) y@(App _ _ _)
        | (P _ cx _, xargs) <- unApply x,
          (P _ cy _, yargs) <- unApply y,
          caseName cx && caseName cy = sameCase ps cx cy xargs yargs

    ceq ps (App _ fx ax) (App _ fy ay) = liftM2 (&&) (ceq ps fx fy) (ceq ps ax ay)
    ceq ps (Constant x) (Constant y) = return (x == y)
    ceq ps (TType x) (TType y) | x == y = return True
    ceq ps (TType (UVal 0)) (TType y) = return True
    ceq ps (TType x) (TType y) = do (v, cs) <- get
                                    put (v, ULE x y : cs)
                                    return True
    ceq ps (UType AllTypes) x = return (isUsableUniverse x)
    ceq ps x (UType AllTypes) = return (isUsableUniverse x)
    ceq ps (UType u) (UType v) = return (u == v)
    ceq ps Erased _ = return True
    ceq ps _ Erased = return True
    ceq ps x y = return False

    caseeq ps (Case _ n cs) (Case _ n' cs') = caseeqA ((n,n'):ps) cs cs'
      where
        caseeqA ps (ConCase x i as sc : rest) (ConCase x' i' as' sc' : rest')
            = do q1 <- caseeq (zip as as' ++ ps) sc sc'
                 q2 <- caseeqA ps rest rest'
                 return $ x == x' && i == i' && q1 && q2
        caseeqA ps (ConstCase x sc : rest) (ConstCase x' sc' : rest')
            = do q1 <- caseeq ps sc sc'
                 q2 <- caseeqA ps rest rest'
                 return $ x == x' && q1 && q2
        caseeqA ps (DefaultCase sc : rest) (DefaultCase sc' : rest')
            = liftM2 (&&) (caseeq ps sc sc') (caseeqA ps rest rest')
        caseeqA ps [] [] = return True
        caseeqA ps _ _ = return False
    caseeq ps (STerm x) (STerm y) = ceq ps x y
    caseeq ps (UnmatchedCase _) (UnmatchedCase _) = return True
    caseeq ps _ _ = return False

    sameDefs ps x y = case (lookupDef x ctxt, lookupDef y ctxt) of
                        ([Function _ xdef], [Function _ ydef])
                              -> ceq ((x,y):ps) xdef ydef
                        ([CaseOp _ _ _ _ _ xd],
                         [CaseOp _ _ _ _ _ yd])
                              -> let (_, xdef) = cases_compiletime xd
                                     (_, ydef) = cases_compiletime yd in
                                       caseeq ((x,y):ps) xdef ydef
                        _ -> return False

    sameCase :: [(Name, Name)] -> Name -> Name -> [Term] -> [Term] ->
                StateT UCs TC Bool
    sameCase ps x y xargs yargs
          = case (lookupDef x ctxt, lookupDef y ctxt) of
                 ([Function _ xdef], [Function _ ydef])
                       -> ceq ((x,y):ps) xdef ydef
                 ([CaseOp _ _ _ _ _ xd],
                  [CaseOp _ _ _ _ _ yd])
                       -> let (xin, xdef) = cases_compiletime xd
                              (yin, ydef) = cases_compiletime yd in
                            do liftM2 (&&)
                                  (do ok <- zipWithM (ceq ps)
                                              (drop (length xin) xargs)
                                              (drop (length yin) yargs)
                                      return (and ok))
                                  (caseeq ((x,y):ps) xdef ydef)
                 _ -> return False

-- SPECIALISATION -----------------------------------------------------------
-- We need too much control to be able to do this by tweaking the main
-- evaluator

spec :: Context -> Ctxt [Bool] -> Env -> TT Name -> Eval (TT Name)
spec ctxt statics genv tm = error "spec undefined"

-- CONTEXTS -----------------------------------------------------------------

{-| A definition is either a simple function (just an expression with a type),
   a constant, which could be a data or type constructor, an axiom or as an
   yet undefined function, or an Operator.
   An Operator is a function which explains how to reduce.
   A CaseOp is a function defined by a simple case tree -}

data Def = Function !Type !Term
         | TyDecl NameType !Type
         | Operator Type Int ([Value] -> Maybe Value)
         | CaseOp CaseInfo
                  !Type
                  ![(Type, Bool)] -- argument types, whether canonical
                  ![Either Term (Term, Term)] -- original definition
                  ![([Name], Term, Term)] -- simplified for totality check definition
                  !CaseDefs
  deriving Generic
--                   [Name] SC -- Compile time case definition
--                   [Name] SC -- Run time cae definitions

data CaseDefs = CaseDefs {
                  cases_compiletime :: !([Name], SC),
                  cases_runtime :: !([Name], SC)
                }
  deriving Generic

data CaseInfo = CaseInfo {
                  case_inlinable :: Bool, -- decided by machine
                  case_alwaysinline :: Bool, -- decided by %inline flag
                  tc_dictionary :: Bool
                }
  deriving Generic

{-!
deriving instance Binary Def
!-}
{-!
deriving instance Binary CaseInfo
!-}
{-!
deriving instance Binary CaseDefs
!-}

instance Show Def where
    show (Function ty tm) = "Function: " ++ show (ty, tm)
    show (TyDecl nt ty) = "TyDecl: " ++ show nt ++ " " ++ show ty
    show (Operator ty _ _) = "Operator: " ++ show ty
    show (CaseOp (CaseInfo inlc inla inlr) ty atys ps_in ps cd)
      = let (ns, sc) = cases_compiletime cd
            (ns', sc') = cases_runtime cd in
          "Case: " ++ show ty ++ " " ++ show ps ++ "\n" ++
                                        "COMPILE TIME:\n\n" ++
                                        show ns ++ " " ++ show sc ++ "\n\n" ++
                                        "RUN TIME:\n\n" ++
                                        show ns' ++ " " ++ show sc' ++ "\n\n" ++
            if inlc then "Inlinable" else "Not inlinable" ++
            if inla then " Aggressively\n" else "\n"

-------

-- Hidden => Programs can't access the name at all
-- Public => Programs can access the name and use at will
-- Frozen => Programs can access the name, which doesn't reduce
-- Private => Programs can't access the name, doesn't reduce internally

data Accessibility = Hidden | Public | Frozen | Private
    deriving (Eq, Ord, Generic)

instance Show Accessibility where
  show Public = "public export"
  show Frozen = "export"
  show Private = "private"
  show Hidden = "hidden"

type Injectivity = Bool

-- | The result of totality checking
data Totality = Total [Int] -- ^ well-founded arguments
              | Productive -- ^ productive
              | Partial PReason
              | Unchecked
              | Generated
    deriving (Eq, Generic)

-- | Reasons why a function may not be total
data PReason = Other [Name] | Itself | NotCovering | NotPositive | UseUndef Name
             | ExternalIO | BelieveMe | Mutual [Name] | NotProductive
    deriving (Show, Eq, Generic)

instance Show Totality where
    show (Total args)= "Total" -- ++ show args ++ " decreasing arguments"
    show Productive = "Productive" -- ++ show args ++ " decreasing arguments"
    show Unchecked = "not yet checked for totality"
    show (Partial Itself) = "possibly not total as it is not well founded"
    show (Partial NotCovering) = "not total as there are missing cases"
    show (Partial NotPositive) = "not strictly positive"
    show (Partial ExternalIO) = "an external IO primitive"
    show (Partial NotProductive) = "not productive"
    show (Partial BelieveMe) = "not total due to use of believe_me in proof"
    show (Partial (Other ns)) = "possibly not total due to: " ++ showSep ", " (map show ns)
    show (Partial (Mutual ns)) = "possibly not total due to recursive path " ++
                                 showSep " --> " (map show ns)
    show (Partial (UseUndef n)) = "possibly not total because it uses the undefined name " ++ show n
    show Generated = "auto-generated"

{-!
deriving instance Binary Accessibility
!-}

{-!
deriving instance Binary Totality
!-}

{-!
deriving instance Binary PReason
!-}

-- Possible attached meta-information for a definition in context
data MetaInformation =
      EmptyMI -- ^ No meta-information
    | DataMI [Int] -- ^ Meta information for a data declaration with position of parameters
  deriving (Eq, Show, Generic)

-- | Contexts used for global definitions and for proof state. They contain
-- universe constraints and existing definitions.
-- Also store maximum RigCount of the name (can't bind a name at multiplicity
-- 1 in a RigW, for example)
data Context = MkContext {
                  next_tvar       :: Int,
                  definitions     :: Ctxt TTDecl
                } deriving (Show, Generic)

type TTDecl = (Def, RigCount, Injectivity, Accessibility, Totality, MetaInformation)

-- | The initial empty context
initContext = MkContext 0 emptyContext


mapDefCtxt :: (Def -> Def) -> Context -> Context
mapDefCtxt f (MkContext t !defs) = MkContext t (mapCtxt f' defs)
   where f' (!d, r, i, a, t, m) = f' (f d, r, i, a, t, m)

-- | Get the definitions from a context
ctxtAlist :: Context -> [(Name, Def)]
ctxtAlist ctxt = map (\(n, (d, r, i, a, t, m)) -> (n, d)) $ toAlist (definitions ctxt)

veval ctxt env t = evalState (eval False ctxt [] env t []) initEval

addToCtxt :: Name -> Term -> Type -> Context -> Context
addToCtxt n tm ty uctxt
    = let ctxt = definitions uctxt
          !ctxt' = addDef n (Function ty tm, RigW, False, Public, Unchecked, EmptyMI) ctxt in
          uctxt { definitions = ctxt' }

setAccess :: Name -> Accessibility -> Context -> Context
setAccess n a uctxt
    = let ctxt = definitions uctxt
          !ctxt' = updateDef n (\ (d, r, i, _, t, m) -> (d, r, i, a, t, m)) ctxt in
          uctxt { definitions = ctxt' }

setInjective :: Name -> Injectivity -> Context -> Context
setInjective n i uctxt
    = let ctxt = definitions uctxt
          !ctxt' = updateDef n (\ (d, r, _, a, t, m) -> (d, r, i, a, t, m)) ctxt in
          uctxt { definitions = ctxt' }

setTotal :: Name -> Totality -> Context -> Context
setTotal n t uctxt
    = let ctxt = definitions uctxt
          !ctxt' = updateDef n (\ (d, r, i, a, _, m) -> (d, r, i, a, t, m)) ctxt in
          uctxt { definitions = ctxt' }

setRigCount :: Name -> RigCount -> Context -> Context
setRigCount n rc uctxt
    = let ctxt = definitions uctxt
          !ctxt' = updateDef n (\ (d, _, i, a, t, m) -> (d, rc, i, a, t, m)) ctxt in
          uctxt { definitions = ctxt' }

setMetaInformation :: Name -> MetaInformation -> Context -> Context
setMetaInformation n m uctxt
    = let ctxt = definitions uctxt
          !ctxt' = updateDef n (\ (d, r, i, a, t, _) -> (d, r, i, a, t, m)) ctxt in
          uctxt { definitions = ctxt' }

addCtxtDef :: Name -> Def -> Context -> Context
addCtxtDef n d c = let ctxt = definitions c
                       !ctxt' = addDef n (d, RigW, False, Public, Unchecked, EmptyMI) $! ctxt in
                       c { definitions = ctxt' }

addTyDecl :: Name -> NameType -> Type -> Context -> Context
addTyDecl n nt ty uctxt
    = let ctxt = definitions uctxt
          !ctxt' = addDef n (TyDecl nt ty, RigW, False, Public, Unchecked, EmptyMI) ctxt in
          uctxt { definitions = ctxt' }

addDatatype :: Datatype Name -> Context -> Context
addDatatype (Data n tag ty unique cons) uctxt
    = let ctxt = definitions uctxt
          ty' = normalise uctxt [] ty
          !ctxt' = addCons 0 cons (addDef n
                     (TyDecl (TCon tag (arity ty')) ty, RigW, True, Public, Unchecked, EmptyMI) ctxt) in
          uctxt { definitions = ctxt' }
  where
    addCons tag [] ctxt = ctxt
    addCons tag ((n, ty) : cons) ctxt
        = let ty' = normalise uctxt [] ty in
              addCons (tag+1) cons (addDef n
                  (TyDecl (DCon tag (arity ty') unique) ty, RigW, True, Public, Unchecked, EmptyMI) ctxt)

-- FIXME: Too many arguments! Refactor all these Bools.
--
-- Issue #1724 on the issue tracker.
-- https://github.com/idris-lang/Idris-dev/issues/1724
addCasedef :: Name -> ErasureInfo -> CaseInfo ->
              Bool -> SC -> -- default case
              Bool -> Bool ->
              [(Type, Bool)] -> -- argument types, whether canonical
              [Int] ->  -- inaccessible arguments
              [Either Term (Term, Term)] ->
              [([Name], Term, Term)] -> -- compile time
              [([Name], Term, Term)] -> -- run time
              Type -> Context -> TC Context
addCasedef n ei ci@(CaseInfo inline alwaysInline tcdict)
           tcase covering reflect asserted argtys inacc
           ps_in ps_ct ps_rt ty uctxt
    = do let ctxt = definitions uctxt
             access = case lookupDefAcc n False uctxt of
                           [(_, acc)] -> acc
                           _ -> Public
         compileTime <- simpleCase tcase covering reflect CompileTime emptyFC inacc argtys ps_ct ei
         runtime <- simpleCase tcase covering reflect RunTime emptyFC inacc argtys ps_rt ei
         ctxt' <- case (compileTime, runtime) of
                    ( CaseDef args_ct sc_ct _,
                     CaseDef args_rt sc_rt _) ->
                       let inl = alwaysInline -- tcdict
                           inlc = (inl || small n args_ct sc_ct) && (not asserted)
                           inlr = inl || small n args_rt sc_rt
                           cdef = CaseDefs (args_ct, sc_ct)
                                           (args_rt, sc_rt)
                           op = (CaseOp (ci { case_inlinable = inlc })
                                                ty argtys ps_in ps_ct cdef,
                                 RigW, False, access, Unchecked, EmptyMI)
                       in return $ addDef n op ctxt
--                    other -> tfail (Msg $ "Error adding case def: " ++ show other)
         return uctxt { definitions = ctxt' }

-- simplify a definition by unfolding interface methods
-- We need this for totality checking, because functions which use interfaces
-- in an implementation definition themselves need to have the implementation
-- inlined or it'll be treated as a higher order function that will potentially
-- loop.
simplifyCasedef :: Name -> [Name] -> [[Name]] -> ErasureInfo -> Context -> TC Context
simplifyCasedef n ufnames umethss ei uctxt
   = do let ctxt = definitions uctxt
        ctxt' <- case lookupCtxt n ctxt of
                   [(CaseOp ci ty atys [] ps _, rc, inj, acc, tot, metainf)] ->
                      return ctxt -- nothing to simplify (or already done...)
                   [(CaseOp ci ty atys ps_in ps cd, rc, inj, acc, tot, metainf)] ->
                      do let ps_in' = map simpl ps_in
                             pdef = map debind ps_in'
                         CaseDef args sc _ <- simpleCase False (STerm Erased) False CompileTime emptyFC [] atys pdef ei
                         return $ addDef n (CaseOp ci
                                              ty atys ps_in' ps (cd { cases_compiletime = (args, sc) }),
                                              rc, inj, acc, tot, metainf) ctxt

                   _ -> return ctxt
        return uctxt { definitions = ctxt' }
  where
    depat acc (Bind n (PVar _ t) sc)
        = depat (n : acc) (instantiate (P Bound n t) sc)
    depat acc x = (acc, x)
    debind (Right (x, y)) = let (vs, x') = depat [] x
                                (_, y') = depat [] y in
                                (vs, x', y')
    debind (Left x)       = let (vs, x') = depat [] x in
                                (vs, x', Impossible)
    simpl (Right (x, y))
         = if null ufnames then Right (x, y)
              else Right (x, unfold uctxt [] (map (\n -> (n, 1)) (uns y)) y)
    simpl t = t

    -- Unfold the given name, interface methdods, and any function which uses it as
    -- an argument directly. This is specifically for finding applications of
    -- interface dictionaries and inlining them both for totality checking and for
    -- a small performance gain.
    uns tm = getNamesToUnfold ufnames umethss tm

    getNamesToUnfold :: [Name] -> [[Name]] -> Term -> [Name]
    getNamesToUnfold inames ms tm = nub $ inames ++ getNames Nothing tm ++ concat ms
      where
        getNames under fn@(App _ _ _)
            | (f, args) <- unApply fn
                 = let under' = case f of
                                     P _ fn _ -> Just fn
                                     _ -> Nothing
                                  in
                       getNames under f ++ concatMap (getNames under') args
        getNames (Just under) (P _ ref _)
            = if ref `elem` inames then [under] else []
        getNames under (Bind n (Let t v) sc)
            = getNames Nothing t ++
              getNames Nothing v ++
              getNames Nothing sc
        getNames under (Bind n b sc) = getNames Nothing (binderTy b) ++
                                       getNames Nothing sc
        getNames _ _ = []

addOperator :: Name -> Type -> Int -> ([Value] -> Maybe Value) ->
               Context -> Context
addOperator n ty a op uctxt
    = let ctxt = definitions uctxt
          ctxt' = addDef n (Operator ty a op, RigW, False, Public, Unchecked, EmptyMI) ctxt in
          uctxt { definitions = ctxt' }

tfst (a, _, _, _, _, _) = a

lookupNames :: Name -> Context -> [Name]
lookupNames n ctxt
                = let ns = lookupCtxtName n (definitions ctxt) in
                      map fst ns

-- | Get the list of pairs of fully-qualified names and their types that match some name
lookupTyName :: Name -> Context -> [(Name, Type)]
lookupTyName n ctxt = do
  (name, def) <- lookupCtxtName n (definitions ctxt)
  ty <- case tfst def of
                       (Function ty _) -> return ty
                       (TyDecl _ ty) -> return ty
                       (Operator ty _ _) -> return ty
                       (CaseOp _ ty _ _ _ _) -> return ty
  return (name, ty)

-- | Get the pair of a fully-qualified name and its type, if there is a unique one matching the name used as a key.
lookupTyNameExact :: Name -> Context -> Maybe (Name, Type)
lookupTyNameExact n ctxt = listToMaybe [ (nm, v) | (nm, v) <- lookupTyName n ctxt, nm == n ]

-- | Get the types that match some name
lookupTy :: Name -> Context -> [Type]
lookupTy n ctxt = map snd (lookupTyName n ctxt)

-- | Get the single type that matches some name precisely
lookupTyExact :: Name -> Context -> Maybe Type
lookupTyExact n ctxt = fmap snd (lookupTyNameExact n ctxt)

-- | Return true if the given type is a concrete type familyor primitive
-- False it it's a function to compute a type or a variable
isCanonical :: Type -> Context -> Bool
isCanonical t ctxt
     = case unApply t of
            (P _ n _, _) -> isConName n ctxt
            (Constant _, _) -> True
            _ -> False

isConName :: Name -> Context -> Bool
isConName n ctxt = isTConName n ctxt || isDConName n ctxt

isTConName :: Name -> Context -> Bool
isTConName n ctxt
     = case lookupDefExact n ctxt of
         Just (TyDecl (TCon _ _) _) -> True
         _                          -> False

-- | Check whether a resolved name is certainly a data constructor
isDConName :: Name -> Context -> Bool
isDConName n ctxt
     = case lookupDefExact n ctxt of
         Just (TyDecl (DCon _ _ _) _) -> True
         _                            -> False

-- | Check whether any overloading of a name is a data constructor
canBeDConName :: Name -> Context -> Bool
canBeDConName n ctxt
     = or $ do def <- lookupCtxt n (definitions ctxt)
               case tfst def of
                 (TyDecl (DCon _ _ _) _) -> return True
                 _ -> return False

isFnName :: Name -> Context -> Bool
isFnName n ctxt
     = case lookupDefExact n ctxt of
         Just (Function _ _)       -> True
         Just (Operator _ _ _)     -> True
         Just (CaseOp _ _ _ _ _ _) -> True
         _                         -> False

isTCDict :: Name -> Context -> Bool
isTCDict n ctxt
     = case lookupDefExact n ctxt of
         Just (Function _ _)        -> False
         Just (Operator _ _ _)      -> False
         Just (CaseOp ci _ _ _ _ _) -> tc_dictionary ci
         _                          -> False

-- Is the name guarded by constructors in the term?
-- We assume the term is normalised, so no looking under 'let' for example.
conGuarded :: Context -> Name -> Term -> Bool
conGuarded ctxt n tm = guarded n tm
  where
    guarded n (P _ n' _) = n == n'
    guarded n ap@(App _ _ _)
        | (P _ f _, as) <- unApply ap,
          isConName f ctxt = any (guarded n) as
    guarded _ _ = False

lookupP :: Name -> Context -> [Term]
lookupP = lookupP_all False False

lookupP_all :: Bool -> Bool -> Name -> Context -> [Term]
lookupP_all all exact n ctxt
   = do (n', def) <- names
        p <- case def of
          (Function ty tm, _, inj, a, _, _)      -> return (P Ref n' ty, a)
          (TyDecl nt ty, _, _, a, _, _)        -> return (P nt n' ty, a)
          (CaseOp _ ty _ _ _ _, _, inj, a, _, _) -> return (P Ref n' ty, a)
          (Operator ty _ _, _, inj, a, _, _)     -> return (P Ref n' ty, a)
        case snd p of
          Hidden -> if all then return (fst p) else []
          Private -> if all then return (fst p) else []
          _      -> return (fst p)
  where
    names = let ns = lookupCtxtName n (definitions ctxt) in
                if exact
                   then filter (\ (n', d) -> n' == n) ns
                   else ns

lookupDefExact :: Name -> Context -> Maybe Def
lookupDefExact n ctxt = tfst <$> lookupCtxtExact n (definitions ctxt)

lookupDef :: Name -> Context -> [Def]
lookupDef n ctxt = tfst <$> lookupCtxt n (definitions ctxt)

lookupNameDef :: Name -> Context -> [(Name, Def)]
lookupNameDef n ctxt = mapSnd tfst $ lookupCtxtName n (definitions ctxt)
  where mapSnd f [] = []
        mapSnd f ((x,y):xys) = (x, f y) : mapSnd f xys

lookupDefAcc :: Name -> Bool -> Context ->
                [(Def, Accessibility)]
lookupDefAcc n mkpublic ctxt
    = map mkp $ lookupCtxt n (definitions ctxt)
  -- io_bind a special case for REPL prettiness
  where mkp (d, _, inj, a, _, _) = if mkpublic && (not (n == sUN "io_bind" || n == sUN "io_pure"))
                                      then (d, Public) else (d, a)

lookupDefAccExact :: Name -> Bool -> Context ->
                     Maybe (Def, Accessibility)
lookupDefAccExact n mkpublic ctxt
    = fmap mkp $ lookupCtxtExact n (definitions ctxt)
  -- io_bind a special case for REPL prettiness
  where mkp (d, _, inj, a, _, _) = if mkpublic && (not (n == sUN "io_bind" || n == sUN "io_pure"))
                                      then (d, Public) else (d, a)

lookupTotal :: Name -> Context -> [Totality]
lookupTotal n ctxt = map mkt $ lookupCtxt n (definitions ctxt)
  where mkt (d, _, inj, a, t, m) = t

lookupTotalExact :: Name -> Context -> Maybe Totality
lookupTotalExact n ctxt = fmap mkt $ lookupCtxtExact n (definitions ctxt)
  where mkt (d, _, inj, a, t, m) = t

lookupRigCount :: Name -> Context -> [Totality]
lookupRigCount n ctxt = map mkt $ lookupCtxt n (definitions ctxt)
  where mkt (d, _, inj, a, t, m) = t

lookupRigCountExact :: Name -> Context -> Maybe RigCount
lookupRigCountExact n ctxt = fmap mkt $ lookupCtxtExact n (definitions ctxt)
  where mkt (d, rc, inj, a, t, m) = rc

lookupInjectiveExact :: Name -> Context -> Maybe Injectivity
lookupInjectiveExact n ctxt = fmap mkt $ lookupCtxtExact n (definitions ctxt)
  where mkt (d, _, inj, a, t, m) = inj

-- Assume type is at least in whnfArgs form
linearCheck :: Context -> Type -> TC ()
linearCheck ctxt t = checkArgs t
  where
    checkArgs (Bind n (Pi RigW _ ty _) sc)
        = do linearCheckArg ctxt ty
             checkArgs (substV (P Bound n Erased) sc)
    checkArgs (Bind n (Pi _ _ _ _) sc)
          = checkArgs (substV (P Bound n Erased) sc)
    checkArgs _ = return ()

linearCheckArg :: Context -> Type -> TC ()
linearCheckArg ctxt ty = mapM_ checkNameOK (allTTNames ty)
  where
    checkNameOK f
       = case lookupRigCountExact f ctxt of
              Just Rig1 ->
                  tfail $ Msg $ show f ++ " can only appear in a linear binding"
              _ -> return ()

    checkArgs (Bind n (Pi RigW _ ty _) sc)
        = do mapM_ checkNameOK (allTTNames ty)
             checkArgs (substV (P Bound n Erased) sc)
    checkArgs (Bind n (Pi _ _ _ _) sc)
          = checkArgs (substV (P Bound n Erased) sc)
    checkArgs _ = return ()

-- Check if a name is reducible in the type checker. Partial definitions
-- are not reducible (so treated as a constant)
tcReducible :: Name -> Context -> Bool
tcReducible n ctxt = case lookupTotalExact n ctxt of
                          Nothing -> True
                          Just (Partial _) -> False
                          _ -> True

lookupMetaInformation :: Name -> Context -> [MetaInformation]
lookupMetaInformation n ctxt = map mkm $ lookupCtxt n (definitions ctxt)
  where mkm (d, _, inj, a, t, m) = m

lookupNameTotal :: Name -> Context -> [(Name, Totality)]
lookupNameTotal n = map (\(n, (_, _, _, _, t, _)) -> (n, t)) . lookupCtxtName n . definitions


lookupVal :: Name -> Context -> [Value]
lookupVal n ctxt
   = do def <- lookupCtxt n (definitions ctxt)
        case tfst def of
          (Function _ htm) -> return (veval ctxt [] htm)
          (TyDecl nt ty) -> return (VP nt n (veval ctxt [] ty))
          _ -> []

lookupTyEnv :: Name -> Env -> Maybe (Int, RigCount, Type)
lookupTyEnv n env = li n 0 env where
  li n i []           = Nothing
  li n i ((x, r, b): xs)
             | n == x = Just (i, r, binderTy b)
             | otherwise = li n (i+1) xs

-- | Create a unique name given context and other existing names
uniqueNameCtxt :: Context -> Name -> [Name] -> Name
uniqueNameCtxt ctxt n hs
    | n `elem` hs = uniqueNameCtxt ctxt (nextName n) hs
    | [_] <- lookupTy n ctxt = uniqueNameCtxt ctxt (nextName n) hs
    | otherwise = n

uniqueBindersCtxt :: Context -> [Name] -> TT Name -> TT Name
uniqueBindersCtxt ctxt ns (Bind n b sc)
    = let n' = uniqueNameCtxt ctxt n ns in
          Bind n' (fmap (uniqueBindersCtxt ctxt (n':ns)) b) (uniqueBindersCtxt ctxt ns sc)
uniqueBindersCtxt ctxt ns (App s f a) = App s (uniqueBindersCtxt ctxt ns f) (uniqueBindersCtxt ctxt ns a)
uniqueBindersCtxt ctxt ns t = t

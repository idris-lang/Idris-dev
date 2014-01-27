{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances,
             PatternGuards #-}

module Idris.Core.Evaluate(normalise, normaliseTrace, normaliseC, normaliseAll,
                rt_simplify, simplify, specialise, hnf, convEq, convEq',
                Def(..), CaseInfo(..), CaseDefs(..),
                Accessibility(..), Totality(..), PReason(..), MetaInformation(..),
                Context, initContext, ctxtAlist, uconstraints, next_tvar,
                addToCtxt, setAccess, setTotal, setMetaInformation, addCtxtDef, addTyDecl,
                addDatatype, addCasedef, simplifyCasedef, addOperator,
                lookupNames, lookupTy, lookupP, lookupDef, lookupDefAcc, lookupVal,
                mapDefCtxt,
                lookupTotal, lookupNameTotal, lookupMetaInformation, lookupTyEnv, isDConName, isTConName, isConName, isFnName,
                Value(..), Quote(..), initEval, uniqueNameCtxt) where

import Debug.Trace
import Control.Monad.State -- not Strict!
import qualified Data.Binary as B
import Data.Binary hiding (get, put)

import Idris.Core.TT
import Idris.Core.CaseTree

data EvalState = ES { limited :: [(Name, Int)],
                      nexthole :: Int }
  deriving Show

type Eval a = State EvalState a

data EvalOpt = Spec
             | HNF
             | Simplify
             | AtREPL
             | RunTT
  deriving (Show, Eq)

initEval = ES [] 0

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
           | VErased
           | VImpossible
           | VConstant Const
           | VProj Value Int
--            | VLazy Env [Value] Term
           | VTmp Int

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
   = evalState (do val <- eval False ctxt [] env t []
                   quote 0 val) initEval

normaliseAll :: Context -> Env -> TT Name -> TT Name
normaliseAll ctxt env t
   = evalState (do val <- eval False ctxt [] env t [AtREPL]
                   quote 0 val) initEval

normalise :: Context -> Env -> TT Name -> TT Name
normalise = normaliseTrace False

normaliseTrace :: Bool -> Context -> Env -> TT Name -> TT Name
normaliseTrace tr ctxt env t
   = evalState (do val <- eval tr ctxt [] (map finalEntry env) (finalise t) []
                   quote 0 val) initEval

specialise :: Context -> Env -> [(Name, Int)] -> TT Name -> TT Name
specialise ctxt env limits t
   = evalState (do val <- eval False ctxt []
                                 (map finalEntry env) (finalise t)
                                 [Spec]
                   quote 0 val) (initEval { limited = limits })

-- | Like normalise, but we only reduce functions that are marked as okay to
-- inline (and probably shouldn't reduce lets?)
-- 20130908: now only used to reduce for totality checking. Inlining should
-- be done elsewhere.

simplify :: Context -> Env -> TT Name -> TT Name
simplify ctxt env t
   = evalState (do val <- eval False ctxt [(sUN "lazy", 0),
                                           (sUN "assert_smaller", 0),
                                           (sUN "par", 0),
                                           (sUN "prim__syntactic_eq", 0),
                                           (sUN "fork", 0)]
                                 (map finalEntry env) (finalise t)
                                 [Simplify]
                   quote 0 val) initEval

-- | Simplify for run-time (i.e. basic inlining)
rt_simplify :: Context -> Env -> TT Name -> TT Name
rt_simplify ctxt env t
   = evalState (do val <- eval False ctxt [(sUN "lazy", 0),
                                           (sUN "assert_smaller", 0),
                                           (sUN "par", 0),
                                           (sUN "prim__syntactic_eq", 0),
                                           (sUN "prim_fork", 0)]
                                 (map finalEntry env) (finalise t)
                                 [RunTT]
                   quote 0 val) initEval

-- | Reduce a term to head normal form
hnf :: Context -> Env -> TT Name -> TT Name
hnf ctxt env t
   = evalState (do val <- eval False ctxt []
                                 (map finalEntry env)
                                 (finalise t) [HNF]
                   quote 0 val) initEval


-- unbindEnv env (quote 0 (eval ctxt (bindEnv env t)))

finalEntry :: (Name, Binder (TT Name)) -> (Name, Binder (TT Name))
finalEntry (n, b) = (n, fmap finalise b)

bindEnv :: EnvTT n -> TT n -> TT n
bindEnv [] tm = tm
bindEnv ((n, Let t v):bs) tm = Bind n (NLet t v) (bindEnv bs tm)
bindEnv ((n, b):bs)       tm = Bind n b (bindEnv bs tm)

unbindEnv :: EnvTT n -> TT n -> TT n
unbindEnv [] tm = tm
unbindEnv (_:bs) (Bind n b sc) = unbindEnv bs sc

usable :: Bool -- specialising
          -> Name -> [(Name, Int)] -> Eval (Bool, [(Name, Int)])
-- usable _ _ ns@((MN 0 "STOP", _) : _) = return (False, ns)
usable False n [] = return (True, [])
usable True n ns
  = do ES ls num <- get
       case lookup n ls of
            Just 0 -> return (False, ns)
            Just i -> return (True, ns)
            _ -> return (False, ns)
usable False n ns
  = case lookup n ns of
         Just 0 -> return (False, ns)
         Just i -> return $ (True, (n, abs (i-1)) : filter (\ (n', _) -> n/=n') ns)
         _ -> return $ (True, (n, 100) : filter (\ (n', _) -> n/=n') ns)


deduct :: Name -> Eval ()
deduct n = do ES ls num <- get
              case lookup n ls of
                  Just i -> do put $ ES ((n, (i-1)) :
                                           filter (\ (n', _) -> n/=n') ls) num
                  _ -> return ()

-- | Evaluate in a context of locally named things (i.e. not de Bruijn indexed,
-- such as we might have during construction of a proof)

-- The (Name, Int) pair in the arguments is the maximum depth of unfolding of
-- a name. The corresponding pair in the state is the maximum number of
-- unfoldings overall.

eval :: Bool -> Context -> [(Name, Int)] -> Env -> TT Name ->
        [EvalOpt] -> Eval Value
eval traceon ctxt ntimes genv tm opts = ev ntimes [] True [] tm where
    spec = Spec `elem` opts
    simpl = Simplify `elem` opts
    runtime = RunTT `elem` opts
    atRepl = AtREPL `elem` opts
    hnf = HNF `elem` opts

    -- returns 'True' if the function should block
    -- normal evaluation should return false
    blockSimplify (CaseInfo inl dict) n stk
       | RunTT `elem` opts
           = not (inl || dict) || elem n stk
       | Simplify `elem` opts
           = (not (inl || dict) || elem n stk)
             || (n == sUN "prim__syntactic_eq")
       | otherwise = False

    getCases cd | simpl = cases_totcheck cd
                | runtime = cases_runtime cd
                | otherwise = cases_compiletime cd

    ev ntimes stk top env (P _ n ty)
        | Just (Let t v) <- lookup n genv = ev ntimes stk top env v
    ev ntimes_in stk top env (P Ref n ty)
      | not top && hnf = liftM (VP Ref n) (ev ntimes stk top env ty)
      | otherwise
         = do (u, ntimes) <- usable spec n ntimes_in
              if u then
               do let val = lookupDefAcc n (spec || atRepl) ctxt
                  case val of
                    [(Function _ tm, Public)] ->
                           ev ntimes (n:stk) True env tm
                    [(Function _ tm, Hidden)] ->
                           ev ntimes (n:stk) True env tm
                    [(TyDecl nt ty, _)] -> do vty <- ev ntimes stk True env ty
                                              return $ VP nt n vty
                    [(CaseOp ci _ _ _ _ cd, acc)]
                         | (acc /= Frozen) &&
                             null (fst (cases_totcheck cd)) -> -- unoptimised version
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
           = do v' <- ev ntimes stk top env v --(finalise v)
                sc' <- ev ntimes stk top ((n, v') : env) sc
                wknV (-1) sc'
--         | otherwise
--            = do t' <- ev ntimes stk top env t
--                 v' <- ev ntimes stk top env v --(finalise v)
--                 -- use Tmp as a placeholder, then make it a variable reference
--                 -- again when evaluation finished
--                 hs <- get
--                 let vd = nexthole hs
--                 put (hs { nexthole = vd + 1 })
--                 sc' <- ev ntimes stk top (VP Bound (MN vd "vlet") VErased : env) sc
--                 return $ VBLet vd n t' v' sc'
    ev ntimes stk top env (Bind n (NLet t v) sc)
           = do t' <- ev ntimes stk top env (finalise t)
                v' <- ev ntimes stk top env (finalise v)
                sc' <- ev ntimes stk top ((n, v') : env) sc
                return $ VBind True n (Let t' v') (\x -> return sc')
    ev ntimes stk top env (Bind n b sc)
           = do b' <- vbind env b
                let n' = uniqueName n (map fst env)
                return $ VBind True -- (vinstances 0 sc < 2)
                               n' b' (\x -> ev ntimes stk False ((n, x):env) sc)
       where vbind env t
--                  | simpl
--                      = fmapMB (\tm -> ev ((MN 0 "STOP", 0) : ntimes)
--                                          stk top env (finalise tm)) t
--                  | otherwise
                     = fmapMB (\tm -> ev ntimes stk top env (finalise tm)) t
    ev ntimes stk top env (App f a)
           = do f' <- ev ntimes stk False env f
                a' <- ev ntimes stk False env a
                evApply ntimes stk top env [a'] f'
    ev ntimes stk top env (Proj t i)
           = do -- evaluate dictionaries if it means the projection works
                t' <- ev ntimes stk top env t
--                 tfull' <- reapply ntimes stk top env t' []
                return (doProj t' (getValArgs t'))
       where doProj t' (VP (DCon _ _) _ _, args) 
                  | i >= 0 && i < length args = args!!i
             doProj t' _ = VProj t' i

    ev ntimes stk top env (Constant c) = return $ VConstant c
    ev ntimes stk top env Erased    = return VErased
    ev ntimes stk top env Impossible  = return VImpossible
    ev ntimes stk top env (TType i)   = return $ VType i

    evApply ntimes stk top env args (VApp f a)
          = evApply ntimes stk top env (a:args) f
    evApply ntimes stk top env args f
          = apply ntimes stk top env f args

    reapply ntimes stk top env f@(VP Ref n ty) args
       = let val = lookupDefAcc n (spec || atRepl) ctxt in
         case val of
              [(CaseOp ci _ _ _ _ cd, acc)] ->
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

    apply ntimes stk top env (VBind True n (Lam t) sc) (a:as)
         = do a' <- sc a
              app <- apply ntimes stk top env a' as
              wknV (-1) app
    apply ntimes_in stk top env f@(VP Ref n ty) args
      | not top && hnf = case args of
                            [] -> return f
                            _ -> return $ unload env f args
      | otherwise
         = do (u, ntimes) <- usable spec n ntimes_in
              if u then
                 do let val = lookupDefAcc n (spec || atRepl) ctxt
                    case val of
                      [(CaseOp ci _ _ _ _ cd, acc)]
                           | acc /= Frozen -> -- unoptimised version
                       let (ns, tree) = getCases cd in
                         if blockSimplify ci n stk
                           then return $ unload env (VP Ref n ty) args
                           else -- traceWhen runtime (show (n, ns, tree)) $
                                do c <- evCase ntimes n (n:stk) top env ns args tree
                                   case c of
                                      (Nothing, _) -> return $ unload env (VP Ref n ty) args
                                      (Just v, rest) -> evApply ntimes stk top env rest v
                      [(Operator _ i op, _)]  ->
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
                  when spec $ deduct n -- successful, so deduct usages
                  t <- evTree ntimes stk top env (zip ns args') tree
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
    evTree ntimes stk top env amap (Case n alts)
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

    conHeaded tm@(App _ _)
        | (P (DCon _ _) _ _, args) <- unApply tm = True
    conHeaded t = False

    chooseAlt' ntimes  stk env _ (f, args) alts amap
        = do f' <- apply ntimes stk True env f args
             chooseAlt env f' (getValArgs f')
                       alts amap

    chooseAlt :: [(Name, Value)] -> Value -> (Value, [Value]) -> [CaseAlt] ->
                 [(Name, Value)] ->
                 Eval (Maybe ([(Name, Value)], SC))
    chooseAlt env _ (VP (DCon i a) _ _, args) alts amap
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
    chooseAlt env _ (VBind _ _ (Pi s) t, []) alts amap
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
    findConst PtrType (ConCase n 5 [] v : xs) = Just v
    findConst (AType (ATInt ITBig)) (ConCase n 6 [] v : xs) = Just v
    findConst (AType (ATInt (ITFixed ity))) (ConCase n tag [] v : xs)
        | tag == 7 + fromEnum ity = Just v
    findConst (AType (ATInt (ITVec ity count))) (ConCase n tag [] v : xs)
        | tag == (fromEnum ity + 1) * 1000 + count = Just v
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
    quote i (VP nt n v)    = liftM (P nt n) (quote i v)
    quote i (VV x)         = return $ V x
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
    quote i (VApp f a)     = liftM2 App (quote i f) (quote i a)
    quote i (VType u)       = return $ TType u
    quote i VErased        = return $ Erased
    quote i VImpossible    = return $ Impossible
    quote i (VProj v j)    = do v' <- quote i v
                                return (Proj v' j)
    quote i (VConstant c)  = return $ Constant c
    quote i (VTmp x)       = return $ V (i - x - 1)

wknV :: Int -> Value -> Eval Value
wknV i (VV x)         = return $ VV (x + i)
wknV i (VBind red n b sc) = do b' <- fmapMB (wknV i) b
                               return $ VBind red n b' (\x -> do x' <- sc x
                                                                 wknV i x')
wknV i (VApp f a)     = liftM2 VApp (wknV i f) (wknV i a)
wknV i t              = return t

convEq' ctxt x y = evalStateT (convEq ctxt x y) (0, [])

convEq :: Context -> TT Name -> TT Name -> StateT UCs (TC' Err) Bool
convEq ctxt = ceq [] where
    ceq :: [(Name, Name)] -> TT Name -> TT Name -> StateT UCs (TC' Err) Bool
    ceq ps (P xt x _) (P yt y _)
        | x == y || (x, y) `elem` ps || (y,x) `elem` ps = return True
        | otherwise = sameDefs ps x y
    ceq ps x (Bind n (Lam t) (App y (V 0))) = ceq ps x y
    ceq ps (Bind n (Lam t) (App x (V 0))) y = ceq ps x y
    ceq ps x (Bind n (Lam t) (App y (P Bound n' _)))
        | n == n' = ceq ps x y
    ceq ps (Bind n (Lam t) (App x (P Bound n' _))) y
        | n == n' = ceq ps x y
    ceq ps (V x)      (V y)      = return (x == y)
    ceq ps (Bind _ xb xs) (Bind _ yb ys)
                             = liftM2 (&&) (ceqB ps xb yb) (ceq ps xs ys)
        where
            ceqB ps (Let v t) (Let v' t') = liftM2 (&&) (ceq ps v v') (ceq ps t t')
            ceqB ps (Guess v t) (Guess v' t') = liftM2 (&&) (ceq ps v v') (ceq ps t t')
            ceqB ps b b' = ceq ps (binderTy b) (binderTy b')
    ceq ps (App fx ax) (App fy ay)   = liftM2 (&&) (ceq ps fx fy) (ceq ps ax ay)
    ceq ps (Constant x) (Constant y) = return (x == y)
    ceq ps (TType x) (TType y)           = do (v, cs) <- get
                                              put (v, ULE x y : cs)
                                              return True
    ceq ps Erased _ = return True
    ceq ps _ Erased = return True
    ceq ps _ _ = return False

    caseeq ps (Case n cs) (Case n' cs') = caseeqA ((n,n'):ps) cs cs'
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
                  ![Type] -- argument types
                  ![Either Term (Term, Term)] -- original definition
                  ![([Name], Term, Term)] -- simplified for totality check definition
                  !CaseDefs
--                   [Name] SC -- Compile time case definition
--                   [Name] SC -- Run time cae definitions

data CaseDefs = CaseDefs {
                  cases_totcheck :: !([Name], SC),
                  cases_compiletime :: !([Name], SC),
                  cases_inlined :: !([Name], SC),
                  cases_runtime :: !([Name], SC)
                }

data CaseInfo = CaseInfo {
                  case_inlinable :: Bool,
                  tc_dictionary :: Bool
                }

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
    show (CaseOp (CaseInfo inlc inlr) ty atys ps_in ps cd)
      = let (ns, sc) = cases_compiletime cd
            (ns_t, sc_t) = cases_totcheck cd
            (ns', sc') = cases_runtime cd in
          "Case: " ++ show ty ++ " " ++ show ps ++ "\n" ++
                                        "TOTALITY CHECK TIME:\n\n" ++
                                        show ns_t ++ " " ++ show sc_t ++ "\n\n" ++
                                        "COMPILE TIME:\n\n" ++
                                        show ns ++ " " ++ show sc ++ "\n\n" ++
                                        "RUN TIME:\n\n" ++
                                        show ns' ++ " " ++ show sc' ++ "\n\n" ++
            if inlc then "Inlinable\n" else "Not inlinable\n"

-------

-- Frozen => doesn't reduce
-- Hidden => doesn't reduce and invisible to type checker

data Accessibility = Public | Frozen | Hidden
    deriving (Show, Eq)

-- | The result of totality checking
data Totality = Total [Int] -- ^ well-founded arguments
              | Productive -- ^ productive
              | Partial PReason
              | Unchecked
    deriving Eq

-- | Reasons why a function may not be total
data PReason = Other [Name] | Itself | NotCovering | NotPositive | UseUndef Name
             | BelieveMe | Mutual [Name] | NotProductive
    deriving (Show, Eq)

instance Show Totality where
    show (Total args)= "Total" -- ++ show args ++ " decreasing arguments"
    show Productive = "Productive" -- ++ show args ++ " decreasing arguments"
    show Unchecked = "not yet checked for totality"
    show (Partial Itself) = "possibly not total as it is not well founded"
    show (Partial NotCovering) = "not total as there are missing cases"
    show (Partial NotPositive) = "not strictly positive"
    show (Partial NotProductive) = "not productive"
    show (Partial BelieveMe) = "not total due to use of believe_me in proof"
    show (Partial (Other ns)) = "possibly not total due to: " ++ showSep ", " (map show ns)
    show (Partial (Mutual ns)) = "possibly not total due to recursive path " ++
                                 showSep " --> " (map show ns)

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
  deriving (Eq, Show)

-- | Contexts used for global definitions and for proof state. They contain
-- universe constraints and existing definitions.
data Context = MkContext {
                  uconstraints    :: [UConstraint],
                  next_tvar       :: Int,
                  definitions     :: Ctxt (Def, Accessibility, Totality, MetaInformation)
                } deriving Show

-- | The initial empty context
initContext = MkContext [] 0 emptyContext

mapDefCtxt :: (Def -> Def) -> Context -> Context
mapDefCtxt f (MkContext c t defs) = MkContext c t (mapCtxt f' defs)
   where f' (d, a, t, m) = f' (f d, a, t, m)

-- | Get the definitions from a context
ctxtAlist :: Context -> [(Name, Def)]
ctxtAlist ctxt = map (\(n, (d, a, t, m)) -> (n, d)) $ toAlist (definitions ctxt)

veval ctxt env t = evalState (eval False ctxt [] env t []) initEval

addToCtxt :: Name -> Term -> Type -> Context -> Context
addToCtxt n tm ty uctxt
    = let ctxt = definitions uctxt
          ctxt' = addDef n (Function ty tm, Public, Unchecked, EmptyMI) ctxt in
          uctxt { definitions = ctxt' }

setAccess :: Name -> Accessibility -> Context -> Context
setAccess n a uctxt
    = let ctxt = definitions uctxt
          ctxt' = updateDef n (\ (d, _, t, m) -> (d, a, t, m)) ctxt in
          uctxt { definitions = ctxt' }

setTotal :: Name -> Totality -> Context -> Context
setTotal n t uctxt
    = let ctxt = definitions uctxt
          ctxt' = updateDef n (\ (d, a, _, m) -> (d, a, t, m)) ctxt in
          uctxt { definitions = ctxt' }

setMetaInformation :: Name -> MetaInformation -> Context -> Context
setMetaInformation n m uctxt
    = let ctxt = definitions uctxt
          ctxt' = updateDef n (\ (d, a, t, _) -> (d, a, t, m)) ctxt in
          uctxt { definitions = ctxt' }

addCtxtDef :: Name -> Def -> Context -> Context
addCtxtDef n d c = let ctxt = definitions c
                       ctxt' = addDef n (d, Public, Unchecked, EmptyMI) $! ctxt in
                       c { definitions = ctxt' }

addTyDecl :: Name -> NameType -> Type -> Context -> Context
addTyDecl n nt ty uctxt
    = let ctxt = definitions uctxt
          ctxt' = addDef n (TyDecl nt ty, Public, Unchecked, EmptyMI) ctxt in
          uctxt { definitions = ctxt' }

addDatatype :: Datatype Name -> Context -> Context
addDatatype (Data n tag ty cons) uctxt
    = let ctxt = definitions uctxt
          ty' = normalise uctxt [] ty
          ctxt' = addCons 0 cons (addDef n
                    (TyDecl (TCon tag (arity ty')) ty, Public, Unchecked, EmptyMI) ctxt) in
          uctxt { definitions = ctxt' }
  where
    addCons tag [] ctxt = ctxt
    addCons tag ((n, ty) : cons) ctxt
        = let ty' = normalise uctxt [] ty in
              addCons (tag+1) cons (addDef n
                  (TyDecl (DCon tag (arity ty')) ty, Public, Unchecked, EmptyMI) ctxt)

-- FIXME: Too many arguments! Refactor all these Bools.
addCasedef :: Name -> CaseInfo -> Bool -> Bool -> Bool -> Bool ->
              [Type] -> -- argument types
              [Either Term (Term, Term)] ->
              [([Name], Term, Term)] -> -- totality
              [([Name], Term, Term)] -> -- compile time
              [([Name], Term, Term)] -> -- inlined
              [([Name], Term, Term)] -> -- run time
              Type -> Context -> Context
addCasedef n ci@(CaseInfo alwaysInline tcdict)
           tcase covering reflect asserted argtys 
           ps_in ps_tot ps_inl ps_ct ps_rt ty uctxt
    = let ctxt = definitions uctxt
          access = case lookupDefAcc n False uctxt of
                        [(_, acc)] -> acc
                        _ -> Public
          ctxt' = case (simpleCase tcase covering reflect CompileTime emptyFC argtys ps_tot,
                        simpleCase tcase covering reflect CompileTime emptyFC argtys ps_ct,
                        simpleCase tcase covering reflect CompileTime emptyFC argtys ps_inl,
                        simpleCase tcase covering reflect RunTime emptyFC argtys ps_rt) of
                    (OK (CaseDef args_tot sc_tot _),
                     OK (CaseDef args_ct sc_ct _),
                     OK (CaseDef args_inl sc_inl _),
                     OK (CaseDef args_rt sc_rt _)) ->
                       let inl = alwaysInline -- tcdict
                           inlc = (inl || small n args_ct sc_ct) && (not asserted)
                           inlr = inl || small n args_rt sc_rt
                           cdef = CaseDefs (args_tot, sc_tot)
                                           (args_ct, sc_ct)
                                           (args_inl, sc_inl)
                                           (args_rt, sc_rt) in
                           addDef n (CaseOp (ci { case_inlinable = inlc })
                                            ty argtys ps_in ps_tot cdef,
                                      access, Unchecked, EmptyMI) ctxt in
          uctxt { definitions = ctxt' }

-- simplify a definition for totality checking
simplifyCasedef :: Name -> Context -> Context
simplifyCasedef n uctxt
   = let ctxt = definitions uctxt
         ctxt' = case lookupCtxt n ctxt of
              [(CaseOp ci ty atys [] ps _, acc, tot, metainf)] ->
                 ctxt -- nothing to simplify (or already done...)
              [(CaseOp ci ty atys ps_in ps cd, acc, tot, metainf)] ->
                 let ps_in' = map simpl ps_in
                     pdef = map debind ps_in' in
                     case simpleCase False True False CompileTime emptyFC atys pdef of
                       OK (CaseDef args sc _) ->
                          addDef n (CaseOp ci
                                           ty atys ps_in' ps (cd { cases_totcheck = (args, sc) }),
                                    acc, tot, metainf) ctxt
                       Error err -> error (show err)
              _ -> ctxt in
         uctxt { definitions = ctxt' }
  where
    depat acc (Bind n (PVar t) sc)
        = depat (n : acc) (instantiate (P Bound n t) sc)
    depat acc x = (acc, x)
    debind (Right (x, y)) = let (vs, x') = depat [] x
                                (_, y') = depat [] y in
                                (vs, x', y')
    debind (Left x)       = let (vs, x') = depat [] x in
                                (vs, x', Impossible)
    simpl (Right (x, y)) = Right (x, simplify uctxt [] y)
    simpl t = t

addOperator :: Name -> Type -> Int -> ([Value] -> Maybe Value) ->
               Context -> Context
addOperator n ty a op uctxt
    = let ctxt = definitions uctxt
          ctxt' = addDef n (Operator ty a op, Public, Unchecked, EmptyMI) ctxt in
          uctxt { definitions = ctxt' }

tfst (a, _, _, _) = a

lookupNames :: Name -> Context -> [Name]
lookupNames n ctxt
                = let ns = lookupCtxtName n (definitions ctxt) in
                      map fst ns

lookupTy :: Name -> Context -> [Type]
lookupTy n ctxt
                = do def <- lookupCtxt n (definitions ctxt)
                     case tfst def of
                       (Function ty _) -> return ty
                       (TyDecl _ ty) -> return ty
                       (Operator ty _ _) -> return ty
                       (CaseOp _ ty _ _ _ _) -> return ty

isConName :: Name -> Context -> Bool
isConName n ctxt = isTConName n ctxt || isDConName n ctxt

isTConName :: Name -> Context -> Bool
isTConName n ctxt
     = or $ do def <- lookupCtxt n (definitions ctxt)
               case tfst def of
                    (TyDecl (TCon _ _) _) -> return True
                    _ -> return False

isDConName :: Name -> Context -> Bool
isDConName n ctxt
     = or $ do def <- lookupCtxt n (definitions ctxt)
               case tfst def of
                    (TyDecl (DCon _ _) _) -> return True
                    _ -> return False

isFnName :: Name -> Context -> Bool
isFnName n ctxt
     = or $ do def <- lookupCtxt n (definitions ctxt)
               case tfst def of
                    (Function _ _) -> return True
                    (Operator _ _ _) -> return True
                    (CaseOp _ _ _ _ _ _) -> return True
                    _ -> return False

lookupP :: Name -> Context -> [Term]
lookupP n ctxt
   = do def <-  lookupCtxt n (definitions ctxt)
        p <- case def of
          (Function ty tm, a, _, _) -> return (P Ref n ty, a)
          (TyDecl nt ty, a, _, _) -> return (P nt n ty, a)
          (CaseOp _ ty _ _ _ _, a, _, _) -> return (P Ref n ty, a)
          (Operator ty _ _, a, _, _) -> return (P Ref n ty, a)
        case snd p of
            Hidden -> []
            _ -> return (fst p)

lookupDef :: Name -> Context -> [Def]
lookupDef n ctxt = map tfst $ lookupCtxt n (definitions ctxt)

lookupDefAcc :: Name -> Bool -> Context ->
                [(Def, Accessibility)]
lookupDefAcc n mkpublic ctxt
    = map mkp $ lookupCtxt n (definitions ctxt)
  -- io_bind a special case for REPL prettiness
  where mkp (d, a, _, _) = if mkpublic && (not (n == sUN "io_bind" || n == sUN "io_return"))
                             then (d, Public) else (d, a)

lookupTotal :: Name -> Context -> [Totality]
lookupTotal n ctxt = map mkt $ lookupCtxt n (definitions ctxt)
  where mkt (d, a, t, m) = t

lookupMetaInformation :: Name -> Context -> [MetaInformation]
lookupMetaInformation n ctxt = map mkm $ lookupCtxt n (definitions ctxt)
  where mkm (d, a, t, m) = m

lookupNameTotal :: Name -> Context -> [(Name, Totality)]
lookupNameTotal n = map (\(n, (_, _, t, _)) -> (n, t)) . lookupCtxtName n . definitions


lookupVal :: Name -> Context -> [Value]
lookupVal n ctxt
   = do def <- lookupCtxt n (definitions ctxt)
        case tfst def of
          (Function _ htm) -> return (veval ctxt [] htm)
          (TyDecl nt ty) -> return (VP nt n (veval ctxt [] ty))

lookupTyEnv :: Name -> Env -> Maybe (Int, Type)
lookupTyEnv n env = li n 0 env where
  li n i []           = Nothing
  li n i ((x, b): xs)
             | n == x = Just (i, binderTy b)
             | otherwise = li n (i+1) xs

-- | Create a unique name given context and other existing names
uniqueNameCtxt :: Context -> Name -> [Name] -> Name
uniqueNameCtxt ctxt n hs
    | n `elem` hs = uniqueNameCtxt ctxt (nextName n) hs
    | [_] <- lookupTy n ctxt = uniqueNameCtxt ctxt (nextName n) hs
    | otherwise = n

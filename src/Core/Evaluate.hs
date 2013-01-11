{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances,
             PatternGuards #-}

module Core.Evaluate(normalise, normaliseTrace, normaliseC, normaliseAll,
                simplify, specialise, hnf, convEq, convEq',
                Def(..), Accessibility(..), Totality(..), PReason(..),
                Context, initContext, ctxtAlist, uconstraints, next_tvar,
                addToCtxt, setAccess, setTotal, addCtxtDef, addTyDecl, 
                addDatatype, addCasedef, simplifyCasedef, addOperator,
                lookupNames, lookupTy, lookupP, lookupDef, lookupVal, 
                lookupTotal, lookupTyEnv, isConName, isFnName,
                Value(..)) where

import Debug.Trace
import Control.Monad.State
import qualified Data.Binary as B
import Data.Binary hiding (get, put)

import Core.TT
import Core.CaseTree

data EvalState = ES { limited :: [(Name, Int)],
                      steps :: Int -- number of applications/let reductions
                    }

-- Evaluation fails if we hit a boredom threshold - in which case, just return
-- the original (capture the failure in a Maybe)

type Eval a = State EvalState a

data EvalOpt = Spec | HNF | Simplify Bool | AtREPL
  deriving (Show, Eq)

initEval = ES [] 0

step :: Int -> Eval ()
step max = do e <- get
              put (e { steps = steps e + 1 })
              if steps e > max then fail "Threshold exceeded"
                               else return () 

getSteps :: Eval Int
getSteps = do e <- get
              return (steps e)

-- VALUES (as HOAS) ---------------------------------------------------------

data Value = VP NameType Name Value
           | VV Int
           | VBind Name (Binder Value) (Value -> Eval Value)
           | VApp Value Value
           | VType UExp
           | VErased
           | VConstant Const
--            | VLazy Env [Value] Term
           | VTmp Int

data HNF = HP NameType Name (TT Name)
         | HV Int
         | HBind Name (Binder HNF) (HNF -> Eval HNF)
         | HApp HNF [HNF] [TT Name]
         | HType UExp
         | HConstant Const
         | HTmp Int
    deriving Show

instance Show Value where
    show x = show $ evalState (quote 100 x) initEval

instance Show (a -> b) where
    show x = "<<fn>>"

-- THE EVALUATOR ------------------------------------------------------------

-- The environment is assumed to be "locally named" - i.e., not de Bruijn 
-- indexed.
-- i.e. it's an intermediate environment that we have while type checking or
-- while building a proof.

threshold = 1000 -- boredom threshold for evaluation, to prevent infinite typechecking
                 -- in fact it's a maximum recursion depth

-- Normalise fully type checked terms (so, assume all names/let bindings resolved)
normaliseC :: Context -> Env -> TT Name -> TT Name
normaliseC ctxt env t 
   = evalState (do val <- eval False ctxt threshold [] env t []
                   quote 0 val) initEval

normaliseAll :: Context -> Env -> TT Name -> TT Name
normaliseAll ctxt env t 
   = evalState (do val <- eval False ctxt threshold [] env t [AtREPL]
                   quote 0 val) initEval

normalise :: Context -> Env -> TT Name -> TT Name
normalise = normaliseTrace False

normaliseTrace :: Bool -> Context -> Env -> TT Name -> TT Name
normaliseTrace tr ctxt env t 
   = evalState (do val <- eval tr ctxt threshold [] (map finalEntry env) (finalise t) []
                   quote 0 val) initEval

specialise :: Context -> Env -> [(Name, Int)] -> TT Name -> TT Name
specialise ctxt env limits t 
   = evalState (do val <- eval False ctxt threshold limits (map finalEntry env) (finalise t) []
                   quote 0 val) (initEval { limited = limits })

-- Like normalise, but we only reduce functions that are marked as okay to 
-- inline (and probably shouldn't reduce lets?)

simplify :: Context -> Bool -> Env -> TT Name -> TT Name
simplify ctxt runtime env t 
   = evalState (do val <- eval False ctxt threshold [(UN "lazy", 0),
                                                     (UN "par", 0),
                                                     (UN "fork", 0)] 
                                 (map finalEntry env) (finalise t) 
                                 [Simplify runtime]
                   quote 0 val) initEval

hnf :: Context -> Env -> TT Name -> TT Name
hnf ctxt env t 
   = evalState (do val <- eval False ctxt threshold [] 
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

usable :: Bool -> Name -> [(Name, Int)] -> (Bool, [(Name, Int)])
usable _ _ ns@((MN 0 "STOP", _) : _) = (False, ns)
usable True (UN "io_bind") ns = (False, ns)
usable s n [] = (True, [])
usable s n ns = case lookup n ns of
                  Just 0 -> (False, ns)
                  Just i -> (True, (n, abs (i-1)) : filter (\ (n', _) -> n/=n') ns)
                  _ -> if s then (True, (n, 0) : filter (\ (n', _) -> n/=n') ns)
                            else (True, (n, 100) : filter (\ (n', _) -> n/=n') ns)

reduction :: Eval ()
reduction = do ES ns s <- get
               put (ES ns (s+1))

-- Evaluate in a context of locally named things (i.e. not de Bruijn indexed,
-- such as we might have during construction of a proof)

eval :: Bool -> Context -> Int -> [(Name, Int)] -> Env -> TT Name -> 
        [EvalOpt] -> Eval Value
eval traceon ctxt maxred ntimes genv tm opts = ev ntimes [] True [] tm where
    spec = Spec `elem` opts
    simpl = Simplify True `elem` opts
    atRepl = AtREPL `elem` opts
    hnf = HNF `elem` opts

    canSimplify inl inr n stk 
       =    (Simplify False `elem` opts && (not inl || elem n stk))
         || (Simplify True `elem` opts && (not inr || elem n stk))

    ev ntimes stk top env (P _ n ty)
        | Just (Let t v) <- lookup n genv = do when (not atRepl) $ step maxred
                                               ev ntimes stk top env v 
    ev ntimes_in stk top env (P Ref n ty) 
      | not top && hnf = liftM (VP Ref n) (ev ntimes stk top env ty)
      | (True, ntimes) <- usable simpl n ntimes_in
         = do let val = lookupDefAcc Nothing n atRepl ctxt 
              when (not atRepl) $ step maxred
              case val of
                [(Function _ tm, Public)] -> 
                       ev ntimes (n:stk) True env tm
                [(TyDecl nt ty, _)] -> do vty <- ev ntimes stk True env ty
                                          return $ VP nt n vty
                [(CaseOp inl inr _ _ _ [] tree _ _, acc)] 
                     | acc == Public || simpl -> -- unoptimised version
                   if canSimplify inl inr n stk
                        then liftM (VP Ref n) (ev ntimes stk top env ty)
                        else do c <- evCase ntimes (n:stk) top env [] [] tree 
                                case c of
                                    (Nothing, _) -> liftM (VP Ref n) (ev ntimes stk top env ty)
                                    (Just v, _)  -> return v
                _ -> liftM (VP Ref n) (ev ntimes stk top env ty)
    ev ntimes stk top env (P nt n ty)   = liftM (VP nt n) (ev ntimes stk top env ty)
    ev ntimes stk top env (V i) | i < length env = return $ env !! i
                     | otherwise      = return $ VV i 
    ev ntimes stk top env (Bind n (Let t v) sc)
--         | not simpl || vinstances 0 sc < 2
           = do v' <- ev ntimes stk top env v --(finalise v)
                when (not atRepl) $ step maxred
                sc' <- ev ntimes stk top (v' : env) sc
                wknV (-1) sc'
{-        | otherwise -- put this back when the Bind works properly
           = do t' <- ev ntimes stk top env t
                v' <- ev ntimes stk top env v --(finalise v)
                when (not atRepl) $ step maxred
                -- use Tmp as a placeholder, then make it a variable reference
                -- again when evaluation finished
                sc' <- ev ntimes stk top (v' : env) sc
                return $ VBind n (Let t' v') (\x -> return sc') -}
    ev ntimes stk top env (Bind n (NLet t v) sc)
           = do t' <- ev ntimes stk top env (finalise t)
                v' <- ev ntimes stk top env (finalise v)
                when (not atRepl) $ step maxred
                sc' <- ev ntimes stk top (v' : env) sc
                return $ VBind n (Let t' v') (\x -> return sc')
    ev ntimes stk top env (Bind n b sc) 
           = do b' <- vbind env b
                when (not atRepl) $ step maxred
                return $ VBind n b' (\x -> ev ntimes stk False (x:env) sc)
       where vbind env t 
                 | simpl 
                     = fmapMB (\tm -> ev ((MN 0 "STOP", 0) : ntimes) 
                                         stk top env (finalise tm)) t 
                 | otherwise 
                     = fmapMB (\tm -> ev ntimes stk top env (finalise tm)) t
--     ev ntimes stk top env (App (App (P _ laz _) _) a)
--         | laz == UN "lazy"
--            = trace (showEnvDbg genv a) $ ev ntimes stk top env a
    ev ntimes stk top env (App f a) 
           = do f' <- ev ntimes stk False env f
                a' <- ev ntimes stk False env a
                when (not atRepl) $ step maxred
                evApply ntimes stk top env [a'] f'
    ev ntimes stk top env (Constant c) = return $ VConstant c
    ev ntimes stk top env Erased    = return VErased
    ev ntimes stk top env (TType i)   = return $ VType i
    
    evApply ntimes stk top env args (VApp f a) = 
            evApply ntimes stk top env (a:args) f
    evApply ntimes stk top env args f = do when (not atRepl) $ step maxred
                                           apply ntimes stk top env f args

    apply ntimes stk top env f as 
        | length stk > threshold = return $ unload env f as
    apply ntimes stk top env (VBind n (Lam t) sc) (a:as) 
        = do a' <- sc a
             app <- apply ntimes stk top env a' as 
             wknV (-1) app
--     apply ntimes stk False env f args
--         | spec = specApply ntimes stk env f args 
    apply ntimes_in stk top env f@(VP Ref n ty) args
      | not top && hnf = case args of
                            [] -> return f
                            _ -> return $ unload env f args
      | (True, ntimes) <- usable simpl n ntimes_in
        = traceWhen traceon (show stk) $
          do let val = lookupDefAcc Nothing n atRepl ctxt
             case val of
                [(CaseOp inl inr _ _ _ ns tree _ _, acc)]
                     | acc == Public || simpl -> -- unoptimised version
                  if canSimplify inl inr n stk
                     then return $ unload env (VP Ref n ty) args
                     else do c <- evCase ntimes (n:stk) top env ns args tree
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
    apply ntimes stk top env f (a:as) = return $ unload env f (a:as)
    apply ntimes stk top env f []     = return f

--     specApply stk env f@(VP Ref n ty) args
--         = case lookupCtxt Nothing n statics of
--                 [as] -> if or as 
--                           then trace (show (n, map fst (filter (\ (_, s) -> s) (zip args as)))) $ 
--                                 return $ unload env f args
--                           else return $ unload env f args
--                 _ -> return $ unload env f args
--     specApply stk env f args = return $ unload env f args

    unload env f [] = f
    unload env f (a:as) = unload env (VApp f a) as

    evCase ntimes stk top env ns args tree
        | length ns <= length args 
             = do let args' = take (length ns) args
                  let rest  = drop (length ns) args
                  t <- evTree ntimes stk top env 
                              (zipWith (\n t -> (n, t)) ns args') tree
                  return (t, rest)
        | otherwise = return (Nothing, args)

    evTree :: [(Name, Int)] -> [Name] -> Bool -> 
              [Value] -> [(Name, Value)] -> SC -> Eval (Maybe Value)
    evTree ntimes stk top env amap (UnmatchedCase str) = return Nothing
    evTree ntimes stk top env amap (STerm tm) 
        = do let etm = pToVs (map fst amap) tm
             etm' <- ev ntimes stk (not (conHeaded tm)) 
                                   (map snd amap ++ env) etm
             return $ Just etm'
    evTree ntimes stk top env amap (Case n alts)
        = case lookup n amap of
            Just v -> do c <- chooseAlt env v (getValArgs v) alts amap
                         case c of
                            Just (altmap, sc) -> evTree ntimes stk top env altmap sc
                            _ -> do c' <- chooseAlt' ntimes stk env v (getValArgs v) alts amap
                                    case c' of
                                        Just (altmap, sc) -> evTree ntimes stk top env altmap sc
                                        _ -> return Nothing
            _ -> return Nothing

    conHeaded tm@(App _ _) 
        | (P (DCon _ _) _ _, args) <- unApply tm = True
    conHeaded t = False

    chooseAlt' ntimes  stk env _ (f, args) alts amap
        = do f' <- apply ntimes stk True env f args
             chooseAlt env f' (getValArgs f') alts amap

    chooseAlt :: [Value] -> Value -> (Value, [Value]) -> [CaseAlt] -> [(Name, Value)] ->
                 Eval (Maybe ([(Name, Value)], SC))
    chooseAlt env _ (VP (DCon i a) _ _, args) alts amap
        | Just (ns, sc) <- findTag i alts = return $ Just (updateAmap (zip ns args) amap, sc)
        | Just v <- findDefault alts      = return $ Just (amap, v)
    chooseAlt env _ (VP (TCon i a) _ _, args) alts amap
        | Just (ns, sc) <- findTag i alts = return $ Just (updateAmap (zip ns args) amap, sc)
        | Just v <- findDefault alts      = return $ Just (amap, v)
    chooseAlt env _ (VConstant c, []) alts amap
        | Just v <- findConst c alts      = return $ Just (amap, v)
        | Just v <- findDefault alts      = return $ Just (amap, v)
    chooseAlt _ _ _ _ _                     = return Nothing

    -- Replace old variable names in the map with new matches
    -- (This is possibly unnecessary since we make unique names and don't
    -- allow repeated variables...?)
    updateAmap newm amap 
       = newm ++ filter (\ (x, _) -> not (elem x (map fst newm))) amap
    findTag i [] = Nothing
    findTag i (ConCase n j ns sc : xs) | i == j = Just (ns, sc)
    findTag i (_ : xs) = findTag i xs

    findDefault [] = Nothing
    findDefault (DefaultCase sc : xs) = Just sc
    findDefault (_ : xs) = findDefault xs 

    findConst c [] = Nothing
    findConst c (ConstCase c' v : xs) | c == c' = Just v
    findConst IType   (ConCase n 1 [] v : xs) = Just v 
    findConst FlType  (ConCase n 2 [] v : xs) = Just v 
    findConst ChType  (ConCase n 3 [] v : xs) = Just v 
    findConst StrType (ConCase n 4 [] v : xs) = Just v 
    findConst PtrType (ConCase n 5 [] v : xs) = Just v 
    findConst c (_ : xs) = findConst c xs

    getValArgs tm = getValArgs' tm []
    getValArgs' (VApp f a) as = getValArgs' f (a:as)
    getValArgs' f as = (f, as)

tmpToV i (VTmp 0) = return $ VV i
tmpToV i (VP nt n v) = liftM (VP nt n) (tmpToV i v)
                          
tmpToV i (VBind n b sc) = do b' <- fmapMB (tmpToV i) b
                             let sc' = \x -> do x' <- sc x
                                                tmpToV (i + 1) x'
                             return (VBind n b' sc')
tmpToV i (VApp f a) = liftM2 VApp (tmpToV i f) (tmpToV i a)
tmpToV i x = return x

class Quote a where
    quote :: Int -> a -> Eval (TT Name)

instance Quote Value where
    quote i (VP nt n v)    = liftM (P nt n) (quote i v)
    quote i (VV x)         = return $ V x
    quote i (VBind n b sc) = do sc' <- sc (VTmp i)
                                b' <- quoteB b
                                liftM (Bind n b') (quote (i+1) sc')
       where quoteB t = fmapMB (quote i) t
    quote i (VApp f a)     = liftM2 App (quote i f) (quote i a)
    quote i (VType u)       = return $ TType u
    quote i VErased        = return $ Erased
    quote i (VConstant c)  = return $ Constant c
    quote i (VTmp x)       = return $ V (i - x - 1)

instance Quote HNF where
    quote i (HP nt n t)     = return (P nt n t)
    quote i (HV x)          = return $ V x
    quote i (HBind n b sc)  = do sc' <- sc (HTmp i)
                                 b' <- quoteB b
                                 liftM (Bind n b') (quote (i+1) sc')
        where quoteB t = fmapMB (quote i) t
    quote i (HApp f env as) = do f' <- quote i f
                                 as' <- mapM (iEnv env) as
                                 return $ mkApp f' as'
        where iEnv [] a = return a
              iEnv (x:xs) a = do x' <- quote i x
                                 iEnv xs (weakenTm (-1) (instantiate x' a))
    quote i (HType u)        = return $ TType u
    quote i (HConstant c)   = return $ Constant c
    quote i (HTmp x)        = return $ V (i - x - 1)

wknV :: Int -> Value -> Eval Value
wknV i (VV x)         = return $ VV (x + i)
wknV i (VBind n b sc) = do b' <- fmapMB (wknV i) b
                           return $ VBind n b' (\x -> do x' <- sc x
                                                         wknV i x')
wknV i (VApp f a)     = liftM2 VApp (wknV i f) (wknV i a)
wknV i t              = return t

wknH :: Int -> HNF -> Eval HNF
wknH i (HV x)          = return $ HV (x + i)
wknH i (HBind n b sc)  = do b' <- fmapMB (wknH i) b
                            return $ HBind n b' (\x -> do x' <- sc x
                                                          wknH i x') 
wknH i (HApp f env as) = liftM3 HApp (wknH i f) (return env) 
                                                (return as)
wknH i t               = return t

-- HEAD NORMAL FORM ---------------------------------------------------------

eval_hnf :: Context -> Ctxt [Bool] -> Env -> TT Name -> Eval HNF
eval_hnf ctxt statics genv tm = ev [] tm where
    ev :: [HNF] -> TT Name -> Eval HNF
    ev env (P _ n ty) 
        | Just (Let t v) <- lookup n genv = ev env v
    ev env (P Ref n ty) = case lookupDef Nothing n ctxt of
        [Function _ t]           -> ev env t
        [TyDecl nt ty]           -> return $ HP nt n ty
        [CaseOp inl _ _ _ _ [] tree _ _] ->
            do c <- evCase env [] [] tree
               case c of
                   (Nothing, _, _) -> return $ HP Ref n ty
                   (Just v, _, _)  -> return v
        _ -> return $ HP Ref n ty
    ev env (P nt n ty) = return $ HP nt n ty
    ev env (V i) | i < length env = return $ env !! i
                 | otherwise      = return $ HV i
    ev env (Bind n (Let t v) sc)
        = do v' <- ev env (finalise v)
             sc' <- ev (v' : env) sc
             wknH (-1) sc'
    ev env (Bind n b sc)
        = do b' <- hbind env b
             return $ HBind n b' (\x -> ev (x : env) sc)
      where hbind env t = fmapMB (\tm -> ev env (finalise tm)) t
    ev env (App f a) = evApply env [a] f
    ev env (Constant c) = return $ HConstant c
    ev env (TType i) = return $ HType i

    evApply env args (App f a) = evApply env (a : args) f
    evApply env args f = do f' <- ev env f
                            apply env f' args

    apply env (HBind n (Lam t) sc) (a:as) = do a' <- ev env a
                                               sc' <- sc a'
                                               app <- apply env sc' as
                                               wknH (-1) app
    apply env (HP Ref n ty) args
        | [CaseOp _ _ _ _ _ ns tree _ _] <- lookupDef Nothing n ctxt
            = do c <- evCase env ns args tree
                 case c of
                    (Nothing, _, env') -> return $ unload env' (HP Ref n ty) args
                    (Just v, rest, env') -> do v' <- quote 0 v
                                               apply env' v rest
--         | Just (Operator _ i op) <- lookupDef n ctxt
--             = if (i <= length args)
--                  then case op (take i args) of
--                     Nothing -> return $ unload env (HP Ref n ty) args
--                     Just v -> evApply env (drop i args) v
--                  else return $ unload env (HP Ref n ty) args
    apply env f (a:as) = return $ unload env f (a:as)
    apply env f []     = return f
    
    unload env f [] = f
    unload env f as = HApp f env as

    evCase env ns args tree
        | length ns <= length args 
             = do let args' = take (length ns) args
                  let rest  = drop (length ns) args
                  (t, env') <- evTree env (zipWith (\n t -> (n, t)) ns args') tree
                  return (t, rest, env')
        | otherwise = return (Nothing, args, env)

    evTree :: [HNF] -> [(Name, TT Name)] -> SC -> Eval (Maybe HNF, [HNF])
    evTree env amap (UnmatchedCase str) = return (Nothing, env)
    evTree env amap (STerm tm) 
        = do let etm = pToVs (map fst amap) tm
             amap' <- mapM (ev env) (map snd amap)
             envw <- mapM (wknH (length amap)) env
             let env' = amap' ++ envw
             etm' <- trace (show etm) $ ev env' etm
             etmq <- quote 0 etm'
             trace ("Ev: " ++ show (etm, etmq)) $ return $ (Just etm', env')
    evTree env amap (Case n alts)
        = case lookup n amap of
             Just v -> do v' <- ev env v
                          case chooseAlt v' (getValArgs v') alts amap of
                            Just (altmap, sc) -> evTree env altmap sc
                            _ -> return (Nothing, env)

    chooseAlt :: HNF -> (HNF, [HNF], [TT Name]) -> 
                 [CaseAlt] -> [(Name, TT Name)] ->
                 Maybe ([(Name, TT Name)], SC)
    chooseAlt _ (HP (DCon i a) _ _, env, args) alts amap
        | Just (ns, sc) <- findTag i alts = Just (updateAmap (zip ns args) amap, sc)
        | Just v <- findDefault alts      = Just (amap, v)
    chooseAlt _ (HP (TCon i a) _ _, env, args) alts amap
        | Just (ns, sc) <- findTag i alts = Just (updateAmap (zip ns args) amap, sc)
        | Just v <- findDefault alts      = Just (amap, v)
    chooseAlt _ (HConstant c, env, []) alts amap
        | Just v <- findConst c alts      = Just (amap, v)
        | Just v <- findDefault alts      = Just (amap, v)
    chooseAlt _ _ _ _                     = Nothing

    -- Replace old variable names in the map with new matches
    -- (This is possibly unnecessary since we make unique names and don't
    -- allow repeated variables...?)
    updateAmap newm amap 
       = newm ++ filter (\ (x, _) -> not (elem x (map fst newm))) amap
    findTag i [] = Nothing
    findTag i (ConCase n j ns sc : xs) | i == j = Just (ns, sc)
    findTag i (_ : xs) = findTag i xs

    findDefault [] = Nothing
    findDefault (DefaultCase sc : xs) = Just sc
    findDefault (_ : xs) = findDefault xs 

    findConst c [] = Nothing
    findConst c (ConstCase c' v : xs) | c == c' = Just v
    findConst IType   (ConCase n 1 [] v : xs) = Just v 
    findConst FlType  (ConCase n 2 [] v : xs) = Just v 
    findConst ChType  (ConCase n 3 [] v : xs) = Just v 
    findConst StrType (ConCase n 4 [] v : xs) = Just v 
    findConst PtrType (ConCase n 5 [] v : xs) = Just v 
    findConst W8Type  (ConCase n 6 [] v : xs) = Just v
    findConst W16Type (ConCase n 7 [] v : xs) = Just v
    findConst c (_ : xs) = findConst c xs

    getValArgs (HApp t env args) = (t, env, args)
    getValArgs t = (t, [], [])

convEq' ctxt x y = evalStateT (convEq ctxt x y) (0, [])

convEq :: Context -> TT Name -> TT Name -> StateT UCs TC Bool
convEq ctxt = ceq [] where
    ceq :: [(Name, Name)] -> TT Name -> TT Name -> StateT UCs TC Bool
    ceq ps (P xt x _) (P yt y _) 
        | (xt == yt && x ==y ) || (x, y) `elem` ps || (y,x) `elem` ps = return True
        | otherwise = sameDefs ps x y
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

    sameDefs ps x y = case (lookupDef Nothing x ctxt, lookupDef Nothing y ctxt) of
                        ([Function _ xdef], [Function _ ydef])
                              -> ceq ((x,y):ps) xdef ydef
                        ([CaseOp _ _ _ _ _ _ xdef _ _],   
                         [CaseOp _ _ _ _ _ _ ydef _ _])
                              -> caseeq ((x,y):ps) xdef ydef
                        _ -> return False

-- SPECIALISATION -----------------------------------------------------------
-- We need too much control to be able to do this by tweaking the main 
-- evaluator

spec :: Context -> Ctxt [Bool] -> Env -> TT Name -> Eval (TT Name)
spec ctxt statics genv tm = error "spec undefined" 

-- CONTEXTS -----------------------------------------------------------------

{- A definition is either a simple function (just an expression with a type),
   a constant, which could be a data or type constructor, an axiom or as an
   yet undefined function, or an Operator.
   An Operator is a function which explains how to reduce. 
   A CaseOp is a function defined by a simple case tree -}
   
data Def = Function Type Term
         | TyDecl NameType Type 
         | Operator Type Int ([Value] -> Maybe Value)
         | CaseOp Bool Bool -- compile-time/run-time inlinable
                  Type 
                  [Either Term (Term, Term)] -- original definition
                  [([Name], Term, Term)] -- simplified definition
                  [Name] SC -- Compile time case definition
                  [Name] SC -- Run time cae definitions
{-! 
deriving instance Binary Def 
!-}

instance Show Def where
    show (Function ty tm) = "Function: " ++ show (ty, tm)
    show (TyDecl nt ty) = "TyDecl: " ++ show nt ++ " " ++ show ty
    show (Operator ty _ _) = "Operator: " ++ show ty
    show (CaseOp inlc inlr ty ps_in ps ns sc ns' sc') 
        = "Case: " ++ show ty ++ " " ++ show ps ++ "\n" ++ 
                                        show ns ++ " " ++ show sc ++ "\n" ++
                                        show ns' ++ " " ++ show sc' ++ "\n" ++
            if inlc then "Inlinable\n" else "Not inlinable\n"

-- We need this for serialising Def. Fortunately, it never gets used because
-- we'll never serialise a primitive operator

instance Binary (a -> b) where
    put x = return ()
    get = error "Getting a function"

------- 

-- Frozen => doesn't reduce
-- Hidden => doesn't reduce and invisible to type checker

data Accessibility = Public | Frozen | Hidden
    deriving (Show, Eq)

data Totality = Total [Int] -- well-founded arguments
              | Productive
              | Partial PReason
              | Unchecked
    deriving Eq

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

data Context = MkContext { 
                  uconstraints :: [UConstraint],
                  next_tvar    :: Int,
                  definitions  :: Ctxt (Def, Accessibility, Totality) 
                }

initContext = MkContext [] 0 emptyContext

ctxtAlist :: Context -> [(Name, Def)]
ctxtAlist ctxt = map (\(n, (d, a, t)) -> (n, d)) $ toAlist (definitions ctxt)

veval ctxt env t = evalState (eval False ctxt threshold [] env t []) initEval

addToCtxt :: Name -> Term -> Type -> Context -> Context
addToCtxt n tm ty uctxt 
    = let ctxt = definitions uctxt 
          ctxt' = addDef n (Function ty tm, Public, Unchecked) ctxt in
          uctxt { definitions = ctxt' } 

setAccess :: Name -> Accessibility -> Context -> Context
setAccess n a uctxt
    = let ctxt = definitions uctxt
          ctxt' = updateDef n (\ (d, _, t) -> (d, a, t)) ctxt in
          uctxt { definitions = ctxt' }

setTotal :: Name -> Totality -> Context -> Context
setTotal n t uctxt
    = let ctxt = definitions uctxt
          ctxt' = updateDef n (\ (d, a, _) -> (d, a, t)) ctxt in
          uctxt { definitions = ctxt' }

addCtxtDef :: Name -> Def -> Context -> Context
addCtxtDef n d c = let ctxt = definitions c
                       ctxt' = addDef n (d, Public, Unchecked) ctxt in
                       c { definitions = ctxt' }

addTyDecl :: Name -> Type -> Context -> Context
addTyDecl n ty uctxt 
    = let ctxt = definitions uctxt
          ctxt' = addDef n (TyDecl Ref ty, Public, Unchecked) ctxt in
          uctxt { definitions = ctxt' }

addDatatype :: Datatype Name -> Context -> Context
addDatatype (Data n tag ty cons) uctxt
    = let ctxt = definitions uctxt 
          ty' = normalise uctxt [] ty
          ctxt' = addCons 0 cons (addDef n 
                    (TyDecl (TCon tag (arity ty')) ty, Public, Unchecked) ctxt) in
          uctxt { definitions = ctxt' }
  where
    addCons tag [] ctxt = ctxt
    addCons tag ((n, ty) : cons) ctxt 
        = let ty' = normalise uctxt [] ty in
              addCons (tag+1) cons (addDef n
                  (TyDecl (DCon tag (arity ty')) ty, Public, Unchecked) ctxt)

addCasedef :: Name -> Bool -> Bool -> Bool -> Bool ->
              [Either Term (Term, Term)] -> 
              [([Name], Term, Term)] -> 
              [([Name], Term, Term)] ->
              Type -> Context -> Context
addCasedef n alwaysInline tcase covering asserted ps_in ps psrt ty uctxt 
    = let ctxt = definitions uctxt
          access = case lookupDefAcc Nothing n False uctxt of
                        [(_, acc)] -> acc
                        _ -> Public
          ctxt' = case (simpleCase tcase covering CompileTime (FC "" 0) ps, 
                        simpleCase tcase covering RunTime (FC "" 0) psrt) of
                    (OK (CaseDef args sc _), OK (CaseDef args' sc' _)) -> 
                       let inl = alwaysInline 
                           inlc = (inl || small n args sc') && (not asserted) 
                           inlr = inl || small n args sc' in
                           addDef n (CaseOp inlc inlr 
                                            ty ps_in ps args sc args' sc',
                                      access, Unchecked) ctxt in
          uctxt { definitions = ctxt' }

simplifyCasedef :: Name -> Context -> Context
simplifyCasedef n uctxt
   = let ctxt = definitions uctxt
         ctxt' = case lookupCtxt Nothing n ctxt of
              [(CaseOp inl inr ty [] ps args sc args' sc', acc, tot)] ->
                 ctxt -- nothing to simplify (or already done...)
              [(CaseOp inl inr ty ps_in ps args sc args' sc', acc, tot)] ->
                 let pdef = map debind $ map simpl ps_in in
                     case simpleCase False True CompileTime (FC "" 0) pdef of
                       OK (CaseDef args sc _) ->
                          addDef n (CaseOp inl inr 
                                           ty ps_in ps args sc args' sc',
                                    acc, tot) ctxt 
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
    simpl (Right (x, y)) = Right (x, simplify uctxt False [] y)
    simpl t = t

addOperator :: Name -> Type -> Int -> ([Value] -> Maybe Value) -> 
               Context -> Context
addOperator n ty a op uctxt
    = let ctxt = definitions uctxt 
          ctxt' = addDef n (Operator ty a op, Public, Unchecked) ctxt in
          uctxt { definitions = ctxt' }

tfst (a, _, _) = a

lookupNames :: Maybe [String] -> Name -> Context -> [Name]
lookupNames root n ctxt
                = let ns = lookupCtxtName root n (definitions ctxt) in
                      map fst ns

lookupTy :: Maybe [String] -> Name -> Context -> [Type]
lookupTy root n ctxt 
                = do def <- lookupCtxt root n (definitions ctxt)
                     case tfst def of
                       (Function ty _) -> return ty
                       (TyDecl _ ty) -> return ty
                       (Operator ty _ _) -> return ty
                       (CaseOp _ _ ty _ _ _ _ _ _) -> return ty

isConName :: Maybe [String] -> Name -> Context -> Bool
isConName root n ctxt 
     = or $ do def <- lookupCtxt root n (definitions ctxt)
               case tfst def of
                    (TyDecl (DCon _ _) _) -> return True
                    (TyDecl (TCon _ _) _) -> return True
                    _ -> return False

isFnName :: Maybe [String] -> Name -> Context -> Bool
isFnName root n ctxt 
     = or $ do def <- lookupCtxt root n (definitions ctxt)
               case tfst def of
                    (Function _ _) -> return True
                    (Operator _ _ _) -> return True
                    (CaseOp _ _ _ _ _ _ _ _ _) -> return True
                    _ -> return False

lookupP :: Maybe [String] -> Name -> Context -> [Term]
lookupP root n ctxt 
   = do def <-  lookupCtxt root n (definitions ctxt)
        p <- case def of
          (Function ty tm, a, _) -> return (P Ref n ty, a)
          (TyDecl nt ty, a, _) -> return (P nt n ty, a)
          (CaseOp _ _ ty _ _ _ _ _ _, a, _) -> return (P Ref n ty, a)
          (Operator ty _ _, a, _) -> return (P Ref n ty, a)
        case snd p of
            Hidden -> []
            _ -> return (fst p)

lookupDef :: Maybe [String] -> Name -> Context -> [Def]
lookupDef root n ctxt = map tfst $ lookupCtxt root n (definitions ctxt)

lookupDefAcc :: Maybe [String] -> Name -> Bool -> Context -> 
                [(Def, Accessibility)]
lookupDefAcc root n mkpublic ctxt 
    = map mkp $ lookupCtxt root n (definitions ctxt)
  where mkp (d, a, _) = if mkpublic then (d, Public) else (d, a)

lookupTotal :: Name -> Context -> [Totality]
lookupTotal n ctxt = map mkt $ lookupCtxt Nothing n (definitions ctxt)
  where mkt (d, a, t) = t

lookupVal :: Maybe [String] -> Name -> Context -> [Value]
lookupVal root n ctxt 
   = do def <- lookupCtxt root n (definitions ctxt)
        case tfst def of
          (Function _ htm) -> return (veval ctxt [] htm)
          (TyDecl nt ty) -> return (VP nt n (veval ctxt [] ty))

lookupTyEnv :: Name -> Env -> Maybe (Int, Type)
lookupTyEnv n env = li n 0 env where
  li n i []           = Nothing
  li n i ((x, b): xs) 
             | n == x = Just (i, binderTy b)
             | otherwise = li n (i+1) xs


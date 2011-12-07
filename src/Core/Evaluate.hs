{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances,
             PatternGuards #-}

module Core.Evaluate(normalise, normaliseC, simplify, specialise, hnf,
                Def(..), 
                Context, initContext, ctxtAlist, uconstraints, next_tvar,
                addToCtxt, addTyDecl, addDatatype, addCasedef, addOperator,
                lookupTy, lookupP, lookupDef, lookupVal, lookupTyEnv,
                Value(..)) where

import Debug.Trace
import Control.Monad.State
import qualified Data.Binary as B
import Data.Binary hiding (get, put)

import Core.TT
import Core.CaseTree

type EvalState = ()
type Eval a = State EvalState a

data EvalOpt = Spec | HNF | Simplify
  deriving (Show, Eq)

-- VALUES (as HOAS) ---------------------------------------------------------

data Value = VP NameType Name Value
           | VV Int
           | VBind Name (Binder Value) (Value -> Eval Value)
           | VApp Value Value
           | VSet UExp
           | VConstant Const
           | VTmp Int

data HNF = HP NameType Name (TT Name)
         | HV Int
         | HBind Name (Binder HNF) (HNF -> Eval HNF)
         | HApp HNF [HNF] [TT Name]
         | HSet UExp
         | HConstant Const
         | HTmp Int
    deriving Show

instance Show Value where
    show x = show $ evalState (quote 10 x) ()

instance Show (a -> b) where
    show x = "<<fn>>"

-- THE EVALUATOR ------------------------------------------------------------

-- The environment is assumed to be "locally named" - i.e., not de Bruijn 
-- indexed.
-- i.e. it's an intermediate environment that we have while type checking or
-- while building a proof.

normaliseC :: Context -> Env -> TT Name -> TT Name
normaliseC ctxt env t 
   = evalState (do val <- eval ctxt emptyContext env t []
                   quote 0 val) ()

normalise :: Context -> Env -> TT Name -> TT Name
normalise ctxt env t 
   = evalState (do val <- eval ctxt emptyContext (map finalEntry env) (finalise t) []
                   quote 0 val) ()

specialise :: Context -> Ctxt [Bool] -> TT Name -> TT Name
specialise ctxt statics t 
   = evalState (do val <- eval ctxt statics [] (finalise t) [Spec]
                   quote 0 val) ()

-- Like normalise, but we only reduce functions that are marked as okay to 
-- inline (and probably shouldn't reduce lets?)

simplify :: Context -> Env -> TT Name -> TT Name
simplify ctxt env t 
   = evalState (do val <- eval ctxt emptyContext (map finalEntry env) (finalise t) [Simplify]
                   quote 0 val) ()

hnf :: Context -> Env -> TT Name -> TT Name
hnf ctxt env t 
   = evalState (do val <- eval ctxt emptyContext (map finalEntry env) (finalise t) [HNF]
                   quote 0 val) ()


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

-- Evaluate in a context of locally named things (i.e. not de Bruijn indexed,
-- such as we might have during construction of a proof)

eval :: Context -> Ctxt [Bool] -> Env -> TT Name -> [EvalOpt] -> Eval Value
eval ctxt statics genv tm opts = ev True [] tm where
    spec = Spec `elem` opts
    simpl = Simplify `elem` opts

    ev top env (P _ n ty)
        | Just (Let t v) <- lookup n genv = ev top env v 
    ev top env (P Ref n ty) = case lookupDef Nothing n ctxt of
        [Function _ tm]          -> ev True env tm
        [TyDecl nt ty]           -> do vty <- ev True env ty
                                       return $ VP nt n vty
        [CaseOp inl _ _ [] tree] ->  
           if simpl && (not inl) 
              then liftM (VP Ref n) (ev top env ty)
              else do c <- evCase top env [] [] tree 
                      case c of
                        (Nothing, _) -> liftM (VP Ref n) (ev top env ty)
                        (Just v, _)  -> return v
        _ -> liftM (VP Ref n) (ev top env ty)
    ev top env (P nt n ty)   = liftM (VP nt n) (ev top env ty)
    ev top env (V i) | i < length env = return $ env !! i
                     | otherwise      = return $ VV i 
    ev top env (Bind n (Let t v) sc)
           = do v' <- ev top env v --(finalise v)
                sc' <- ev top (v' : env) sc
                wknV (-1) sc'
    ev top env (Bind n (NLet t v) sc)
           = do t' <- ev top env (finalise t)
                v' <- ev top env (finalise v)
                sc' <- ev top (v' : env) sc
                return $ VBind n (Let t' v') (\x -> return sc')
    ev top env (Bind n b sc) 
           = do b' <- vbind env b
                return $ VBind n b' (\x -> ev top (x:env) sc)
       where vbind env t = fmapMB (\tm -> ev top env (finalise tm)) t
    ev top env (App f a) = do f' <- ev top env f
                              a' <- ev False env a
                              evApply top env [a'] f'
    ev top env (Constant c) = return $ VConstant c
    ev top env (Set i)   = return $ VSet i
    
    evApply top env args (VApp f a) = 
            evApply top env (a:args) f
    evApply top env args f = apply top env f args

    apply top env (VBind n (Lam t) sc) (a:as) 
        = do a' <- sc a
             app <- apply top env a' as 
             wknV (-1) app
    apply False env f args
        | spec = return $ unload env f args
    apply top env (VP Ref n ty)        args
        | [CaseOp inl _ _ ns tree] <- lookupDef Nothing n ctxt
            = -- traceWhen (n == UN ["interp"]) (show (n, args)) $
              if simpl && (not inl) then return $ unload env (VP Ref n ty) args
                 else do c <- evCase top env ns args tree
                         case c of
                           (Nothing, _) -> return $ unload env (VP Ref n ty) args
                           (Just v, rest) -> evApply top env rest v
        | [Operator _ i op]  <- lookupDef Nothing n ctxt
            = if (i <= length args)
                 then case op (take i args) of
                    Nothing -> return $ unload env (VP Ref n ty) args
                    Just v  -> evApply top env (drop i args) v
                 else return $ unload env (VP Ref n ty) args
    apply top env f (a:as) = return $ unload env f (a:as)
    apply top env f []     = return f

    unload env f [] = f
    unload env f (a:as) = unload env (VApp f a) as

    evCase top env ns args tree
        | length ns <= length args 
             = do let args' = take (length ns) args
                  let rest  = drop (length ns) args
                  t <- evTree top env (zipWith (\n t -> (n, t)) ns args') tree
                  return (t, rest)
        | otherwise = return (Nothing, args)

    evTree :: Bool -> [Value] -> [(Name, Value)] -> SC -> Eval (Maybe Value)
    evTree top env amap (UnmatchedCase str) = return Nothing
    evTree top env amap (STerm tm) 
        = do let etm = pToVs (map fst amap) tm
             etm' <- ev top (map snd amap ++ env) etm
             return $ Just etm'
    evTree top env amap (Case n alts)
        = case lookup n amap of
            Just v -> do c <- chooseAlt env v (getValArgs v) alts amap
                         case c of
                            Just (altmap, sc) -> evTree top env altmap sc
                            _ -> do c' <- chooseAlt' env v (getValArgs v) alts amap
                                    case c' of
                                        Just (altmap, sc) -> evTree top env altmap sc
                                        _ -> return Nothing
            _ -> return Nothing

    chooseAlt' env _ (f, args) alts amap
        = do f' <- apply True env f args
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
    quote i (VSet u)       = return $ Set u
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
    quote i (HSet u)        = return $ Set u
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
        [CaseOp inl _ _ [] tree] ->
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
    ev env (Set i) = return $ HSet i

    evApply env args (App f a) = evApply env (a : args) f
    evApply env args f = do f' <- ev env f
                            apply env f' args

    apply env (HBind n (Lam t) sc) (a:as) = do a' <- ev env a
                                               sc' <- sc a'
                                               app <- apply env sc' as
                                               wknH (-1) app
    apply env (HP Ref n ty) args
        | [CaseOp _ _ _ ns tree] <- lookupDef Nothing n ctxt
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
    findConst c (_ : xs) = findConst c xs

    getValArgs (HApp t env args) = (t, env, args)
    getValArgs t = (t, [], [])

-- SPECIALISATION -----------------------------------------------------------
-- We need too much control to be able to do this by tweaking the main 
-- evaluator

spec :: Context -> Ctxt [Bool] -> Env -> TT Name -> Eval (TT Name)
spec ctxt statics genv tm = undefined 

-- CONTEXTS -----------------------------------------------------------------

{- A definition is either a simple function (just an expression with a type),
   a constant, which could be a data or type constructor, an axiom or as an
   yet undefined function, or an Operator.
   An Operator is a function which explains how to reduce. 
   A CaseOp is a function defined by a simple case tree -}
   
data Def = Function Type Term
         | TyDecl NameType Type 
         | Operator Type Int ([Value] -> Maybe Value)
         | CaseOp Bool Type [(Term, Term)] [Name] SC -- Bool for inlineable

instance Show Def where
    show (Function ty tm) = "Function: " ++ show (ty, tm)
    show (TyDecl nt ty) = "TyDecl: " ++ show nt ++ " " ++ show ty
    show (Operator ty _ _) = "Operator: " ++ show ty
    show (CaseOp _ ty ps ns sc) = "Case: " ++ show ps ++ "\n" ++ 
                                              show ns ++ " " ++ show sc

------- 

data Context = MkContext { uconstraints :: [UConstraint],
                           next_tvar    :: Int,
                           definitions  :: Ctxt Def }

initContext = MkContext [] 0 emptyContext

ctxtAlist :: Context -> [(Name, Def)]
ctxtAlist ctxt = toAlist (definitions ctxt)

veval ctxt env t = evalState (eval ctxt emptyContext env t []) ()

addToCtxt :: Name -> Term -> Type -> Context -> Context
addToCtxt n tm ty uctxt 
    = let ctxt = definitions uctxt 
          ctxt' = addDef n (Function ty tm) ctxt in
          uctxt { definitions = ctxt' } 

addTyDecl :: Name -> Type -> Context -> Context
addTyDecl n ty uctxt 
    = let ctxt = definitions uctxt
          ctxt' = addDef n (TyDecl Ref ty) ctxt in
          uctxt { definitions = ctxt' }

addDatatype :: Datatype Name -> Context -> Context
addDatatype (Data n tag ty cons) uctxt
    = let ctxt = definitions uctxt 
          ty' = normalise uctxt [] ty
          ctxt' = addCons 0 cons (addDef n 
                    (TyDecl (TCon tag (arity ty')) ty) ctxt) in
          uctxt { definitions = ctxt' }
  where
    addCons tag [] ctxt = ctxt
    addCons tag ((n, ty) : cons) ctxt 
        = let ty' = normalise uctxt [] ty in
              addCons (tag+1) cons (addDef n
                  (TyDecl (DCon tag (arity ty')) ty) ctxt)

addCasedef :: Name -> Bool -> Bool -> [(Term, Term)] -> Type -> Context -> Context
addCasedef n alwaysInline tcase ps ty uctxt 
    = let ctxt = definitions uctxt
          ps' = ps -- simpl ps in
          ctxt' = case simpleCase tcase ps' of
                    CaseDef args sc -> let inl = alwaysInline in
                                           addDef n (CaseOp inl ty ps args sc) ctxt in
          uctxt { definitions = ctxt' }
  where simpl [] = []
        simpl ((l,r) : xs) = (l, simplify uctxt [] r) : simpl xs

addOperator :: Name -> Type -> Int -> ([Value] -> Maybe Value) -> Context -> Context
addOperator n ty a op uctxt
    = let ctxt = definitions uctxt 
          ctxt' = addDef n (Operator ty a op) ctxt in
          uctxt { definitions = ctxt' }

lookupTy :: Maybe [String] -> Name -> Context -> [Type]
lookupTy root n ctxt 
                = do def <- lookupCtxt root n (definitions ctxt)
                     case def of
                       (Function ty _) -> return ty
                       (TyDecl _ ty) -> return ty
                       (Operator ty _ _) -> return ty
                       (CaseOp _ ty _ _ _) -> return ty

lookupP :: Maybe [String] -> Name -> Context -> [Term]
lookupP root n ctxt 
   = do def <-  lookupCtxt root n (definitions ctxt)
        case def of
          (Function ty tm) -> return (P Ref n ty)
          (TyDecl nt ty) -> return (P nt n ty)
          (CaseOp _ ty _ _ _) -> return (P Ref n ty)
          (Operator ty _ _) -> return (P Ref n ty)

lookupDef :: Maybe [String] -> Name -> Context -> [Def]
lookupDef root n ctxt = lookupCtxt root n (definitions ctxt)

lookupVal :: Maybe [String] -> Name -> Context -> [Value]
lookupVal root n ctxt 
   = do def <- lookupCtxt root n (definitions ctxt)
        case def of
          (Function _ htm)   -> return (veval ctxt [] htm)
          (TyDecl nt ty) -> return (VP nt n (veval ctxt [] ty))

lookupTyEnv :: Name -> Env -> Maybe (Int, Type)
lookupTyEnv n env = li n 0 env where
  li n i []           = Nothing
  li n i ((x, b): xs) 
             | n == x = Just (i, binderTy b)
             | otherwise = li n (i+1) xs

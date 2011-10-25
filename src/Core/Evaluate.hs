{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances,
             PatternGuards #-}

module Core.Evaluate(normalise,
                Fun(..), Def(..), Context, 
                addToCtxt, addTyDecl, addDatatype, addCasedef, addOperator,
                lookupTy, lookupP, lookupDef, lookupVal, lookupTyEnv,
                Value(..)) where

import Debug.Trace

import Core.TT
import Core.CaseTree

-- VALUES (as HOAS) ---------------------------------------------------------

data Value = VP NameType Name Value
           | VV Int
           | VBind Name (Binder Value) (Value -> Value)
           | VApp Value Value
           | VSet Int
           | VConstant Const
           | VTmp Int

instance Show Value where
    show = show . quote 0

-- THE EVALUATOR ------------------------------------------------------------

-- The environment is assumed to be "locally named" - i.e., not de Bruijn 
-- indexed.
-- i.e. it's an intermediate environment that we have while type checking or
-- while building a proof.

normalise :: Context -> Env -> TT Name -> TT Name
normalise ctxt env t = quote 0 (eval ctxt (map finalEntry env) (finalise t))

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

eval :: Context -> Env -> TT Name -> Value
eval ctxt genv tm = ev [] tm where
    ev env (P _ n ty)
        | Just (Let t v) <- lookup n genv = ev env v 
    ev env (P Ref n ty) = case lookupDef n ctxt of
        Just (Function (Fun _ _ _ v)) -> v
        Just (TyDecl nt ty hty)     -> VP nt n hty
        Just (CaseOp _ _ [] tree)   ->  
              case evCase env [] [] tree of
                   (Nothing, _) -> VP Ref n (ev env ty)
                   (Just v, _)  -> v
        _ -> VP Ref n (ev env ty)
    ev env (P nt n ty)   = VP nt n (ev env ty)
    ev env (V i) | i < length env = env !! i
                 | otherwise      = VV i --error $ "Internal error: V" ++ show i ++ " " 
                                         --   ++ showEnv genv tm ++ "\n" ++ show genv
    ev env (Bind n (Let t v) sc)
           = wknV (-1) $ ev (ev env (finalise v) : env) sc
    ev env (Bind n (NLet t v) sc)
           = VBind n (Let (ev env (finalise t)) (ev env (finalise v))) 
                $ (\x -> ev (ev env v : env) sc)
    ev env (Bind n b sc) = VBind n (vbind env b) (\x -> ev (x:env) sc)
       where vbind env t = fmap (\tm -> ev env (finalise tm)) t
    ev env (App f a) = evApply env [ev env a] (ev env f)
    ev env (Constant c) = VConstant c
    ev env (Set i)   = VSet i
    
    evApply env args (VApp f a) = evApply env (a:args) f
    evApply env args f = apply env f args

    apply env (VBind n (Lam t) sc) (a:as) = wknV (-1) $ apply env (sc a) as
    apply env (VP Ref n ty)        args
        | Just (CaseOp _ _ ns tree) <- lookupDef n ctxt
            = case evCase env ns args tree of
                   (Nothing, _) -> unload env (VP Ref n ty) args
                   (Just v, rest) -> evApply env rest v
        | Just (Operator _ i op)  <- lookupDef n ctxt
            = if (i <= length args)
                then case op (take i args) of
                   Nothing -> unload env (VP Ref n ty) args
                   Just v  -> evApply env (drop i args) v
                else unload env (VP Ref n ty) args
    apply env f                    (a:as) = unload env f (a:as)
    apply env f                    []     = f

    unload env f [] = f
    unload env f (a:as) = unload env (VApp f a) as

    evCase env ns args tree
        | length ns <= length args 
             = let args' = take (length ns) args
                   rest  = drop (length ns) args in
                (evTree env (zipWith (\n t -> (n, t)) ns args') tree, rest)
        | otherwise = (Nothing, args)

    evTree :: [Value] -> [(Name, Value)] -> SC -> Maybe Value
    evTree env amap (UnmatchedCase str) = Nothing
    evTree env amap (STerm tm) 
        = let etm = pToVs (map fst amap) tm in
              Just $ ev (map snd amap ++ env) etm
    evTree env amap (Case n alts)
        = do v <- lookup n amap
             (altmap, sc) <- chooseAlt v (getValArgs v) alts amap
             evTree env altmap sc

    chooseAlt :: Value -> (Value, [Value]) -> [CaseAlt] -> [(Name, Value)] ->
                 Maybe ([(Name, Value)], SC)
    chooseAlt _ (VP (DCon i a) _ _, args) alts amap
        | Just (ns, sc) <- findTag i alts = Just (updateAmap (zip ns args) amap, sc)
        | Just v <- findDefault alts      = Just (amap, v)
    chooseAlt _ (VP (TCon i a) _ _, args) alts amap
        | Just (ns, sc) <- findTag i alts = Just (updateAmap (zip ns args) amap, sc)
        | Just v <- findDefault alts      = Just (amap, v)
    chooseAlt _ (VConstant c, []) alts amap
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

    getValArgs tm = getValArgs' tm []
    getValArgs' (VApp f a) as = getValArgs' f (a:as)
    getValArgs' f as = (f, as)

quote :: Int -> Value -> TT Name
quote i (VP nt n v)    = P nt n (quote i v)
quote i (VV x)         = V x
quote i (VBind n b sc) = Bind n (quoteB b) (quote (i+1) (sc (VTmp i)))
   where quoteB t = fmap (quote i) t
quote i (VApp f a)     = App (quote i f) (quote i a)
quote i (VSet u)       = Set u
quote i (VConstant c)  = Constant c
quote i (VTmp x)       = V (i - x - 1)


wknV :: Int -> Value -> Value
wknV i (VV x)         = VV (x + i)
wknV i (VBind n b sc) = VBind n (fmap (wknV i) b) (\x -> (wknV i (sc x)))
wknV i (VApp f a)     = VApp (wknV i f) (wknV i a)
wknV i t              = t

-- CONTEXTS -----------------------------------------------------------------

data Fun = Fun Type Value Term Value
  deriving Show

{- A definition is either a simple function (just an expression with a type),
   a constant, which could be a data or type constructor, an axiom or as an
   yet undefined function, or an Operator.
   An Operator is a function which explains how to reduce. 
   A CaseOp is a function defined by a simple case tree -}
   
data Def = Function Fun
         | TyDecl NameType Type Value
         | Operator Type Int ([Value] -> Maybe Value)
         | CaseOp Type [(Term, Term)] [Name] SC

instance Show Def where
    show (Function f) = "Function: " ++ show f
    show (TyDecl nt ty val) = "TyDecl: " ++ show nt ++ " " ++ show ty
    show (Operator ty _ _) = "Operator: " ++ show ty
    show (CaseOp ty _ ns sc) = "Case: " ++ show ns ++ " " ++ show sc

------- 

type Context = Ctxt Def

addToCtxt :: Name -> Term -> Type -> Context -> Context
addToCtxt n tm ty ctxt = addDef n (Function (Fun ty (eval ctxt [] ty)
                                             tm (eval ctxt [] tm))) ctxt

addTyDecl :: Name -> Type -> Context -> Context
addTyDecl n ty ctxt = addDef n (TyDecl Ref ty (eval ctxt [] ty)) ctxt

addDatatype :: Datatype Name -> Context -> Context
addDatatype (Data n tag ty cons) ctxt
    = let ty' = normalise ctxt [] ty in
          addCons 0 cons (addDef n 
             (TyDecl (TCon tag (arity ty')) ty (eval ctxt [] ty)) ctxt)
  where
    addCons tag [] ctxt = ctxt
    addCons tag ((n, ty) : cons) ctxt 
        = let ty' = normalise ctxt [] ty in
              addCons (tag+1) cons (addDef n
                  (TyDecl (DCon tag (arity ty')) ty (eval ctxt [] ty)) ctxt)

addCasedef :: Name -> Bool -> [(Term, Term)] -> Type -> Context -> Context
addCasedef n tcase ps ty ctxt 
    = case simpleCase tcase ps of
        CaseDef args sc -> addDef n (CaseOp ty ps args sc) ctxt

addOperator :: Name -> Type -> Int -> ([Value] -> Maybe Value) -> Context -> Context
addOperator n ty a op ctxt
    = addDef n (Operator ty a op) ctxt

lookupTy :: Name -> Context -> Maybe Type
lookupTy n ctxt = do def <- lookupCtxt n ctxt
                     case def of
                       (Function (Fun ty _ _ _)) -> return ty
                       (TyDecl _ ty _) -> return ty
                       (Operator ty _ _) -> return ty
                       (CaseOp ty _ _ _) -> return ty

lookupP :: Name -> Context -> Maybe Term
lookupP n ctxt 
   = do def <-  lookupCtxt n ctxt
        case def of
          (Function (Fun ty _ tm _)) -> return (P Ref n ty)
          (TyDecl nt ty hty) -> return (P nt n ty)
          (CaseOp ty _ _ _) -> return (P Ref n ty)
          (Operator ty _ _) -> return (P Ref n ty)

lookupDef :: Name -> Context -> Maybe Def
lookupDef n ctxt = lookupCtxt n ctxt

lookupVal :: Name -> Context -> Maybe Value
lookupVal n ctxt 
   = do def <- lookupCtxt n ctxt
        case def of
          (Function (Fun _ _ _ htm)) -> return htm
          (TyDecl nt ty hty) -> return (VP nt n hty)

lookupTyEnv :: Name -> Env -> Maybe (Int, Type)
lookupTyEnv n env = li n 0 env where
  li n i []           = Nothing
  li n i ((x, b): xs) 
             | n == x = Just (i, binderTy b)
             | otherwise = li n (i+1) xs


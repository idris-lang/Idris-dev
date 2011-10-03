{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Core.Evaluate(normalise,
                Fun(..), Def(..), Context, toAlist,
                emptyContext, addToCtxt, addConstant, addDatatype,
                lookupTy, lookupP, lookupDef, lookupVal, lookupTyEnv) where

import qualified Data.Map as Map
import Debug.Trace
import Core.Core

-- VALUES (as HOAS) ---------------------------------------------------------

data Value = VP NameType Name Value
           | VV Int
           | VBind Name (Binder Value) (Value -> Value)
           | VApp Value Value
           | VSet Int
           | VTmp Int

instance Show Value where
    show = show . quote 0

-- THE EVALUATOR ------------------------------------------------------------

-- The environment is assumed to be "locally named" - i.e., not de Bruijn 
-- indexed.
-- i.e. it's an intermediate environment that we have while type checking or
-- while building a proof.

normalise :: Context -> Env -> TT Name -> TT Name
normalise ctxt env t = quote 0 (eval ctxt env t)

-- unbindEnv env (quote 0 (eval ctxt (bindEnv env t)))

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
    ev env (P Bound n ty)
        | Just (Let t v) <- lookup n genv = ev env v 
    ev env (P Ref n ty)
        | Just v <- lookupVal n ctxt = v
    ev env (P nt n ty)   = VP nt n (ev env ty)
    ev env (V i) | i < length env = env !! i
                 | otherwise      = error $ "Internal error: V" ++ show i
    ev env (Bind n (Let t v) sc)
           = wknV (-1) $ ev (ev env v : env) sc
    ev env (Bind n (NLet t v) sc)
           = VBind n (Let (ev env t) (ev env v)) $ (\x -> ev (ev env v : env) sc)
    ev env (Bind n b sc) = VBind n (vbind env b) (\x -> ev (x:env) sc)
       where vbind env t = fmap (ev env) t    
    ev env (App f a) = evApply env [a] f
    ev env (Set i)   = VSet i
    
    evApply env args (App f a) = evApply env (a:args) f
    evApply env args f = apply env (ev env f) args

    apply env (VBind n (Lam t) sc) (a:as) = wknV (-1) $ apply env (sc (ev env a)) as
    apply env f                    (a:as) = unload env f (a:as)
    apply env f                    []     = f

    unload env f [] = f
    unload env f (a:as) = unload env (VApp f (ev env a)) as

quote :: Int -> Value -> TT Name
quote i (VP nt n v)    = P nt n (quote i v)
quote i (VV x)         = V x
quote i (VBind n b sc) = Bind n (quoteB b) (quote (i+1) (sc (VTmp i)))
   where quoteB t = fmap (quote i) t
quote i (VApp f a)     = App (quote i f) (quote i a)
quote i (VSet u)       = Set u
quote i (VTmp x)       = V (i - x - 1)


wknV :: Int -> Value -> Value
wknV i (VV x)         = VV (x + i)
wknV i (VBind n b sc) = VBind n (fmap (wknV i) b) (\x -> (wknV i (sc x)))
wknV i (VApp f a)     = VApp (wknV i f) (wknV i a)
wknV i t              = t

-- CONTEXTS -----------------------------------------------------------------

data Fun = Fun Type Value Term Value
  deriving Show

data Def = Function Fun
         | Constant NameType Type Value
  deriving Show

{-
type Context = [(Name, Def)]

emptyContext = []

addDef :: Name -> Def -> Context -> Context
addDef n d ctxt = (n, d) : ctxt

lookupCtxt :: Name -> Context -> Maybe Def
lookupCtxt n c = lookup n c
-}

type Context = Map.Map Name Def
emptyContext = Map.empty

addDef :: Name -> Def -> Context -> Context
addDef = Map.insert

lookupCtxt :: Name -> Context -> Maybe Def
lookupCtxt = Map.lookup

toAlist :: Context -> [(Name, Def)]
toAlist = Map.toList

------- 

addToCtxt :: Name -> Term -> Type -> Context -> Context
addToCtxt n tm ty ctxt = addDef n (Function (Fun ty (eval ctxt [] ty)
                                             tm (eval ctxt [] tm))) ctxt

addConstant :: Name -> Type -> Context -> Context
addConstant n ty ctxt = addDef n (Constant Ref ty (eval ctxt [] ty)) ctxt

addDatatype :: Datatype Name -> Context -> Context
addDatatype (Data n ty cons) ctxt
    = let ty' = normalise ctxt [] ty in
          addCons 0 cons (addDef n 
             (Constant (TCon (arity ty')) ty (eval ctxt [] ty)) ctxt)
  where
    addCons tag [] ctxt = ctxt
    addCons tag ((n, ty) : cons) ctxt 
        = let ty' = normalise ctxt [] ty in
              addCons (tag+1) cons (addDef n
                  (Constant (DCon tag (arity ty')) ty (eval ctxt [] ty)) ctxt)

lookupTy :: Name -> Context -> Maybe Type
lookupTy n ctxt = do def <- lookupCtxt n ctxt
                     case def of
                       (Function (Fun ty _ _ _)) -> return ty
                       (Constant _ ty _) -> return ty

lookupP :: Name -> Context -> Maybe Term
lookupP n ctxt 
   = do def <-  lookupCtxt n ctxt
        case def of
          (Function (Fun ty _ tm _)) -> return (P Ref n ty)
          (Constant nt ty hty) -> return (P nt n ty)

lookupDef :: Name -> Context -> Maybe Term
lookupDef n ctxt
   = do def <-  lookupCtxt n ctxt
        case def of
          (Function (Fun ty _ tm _)) -> return tm
          (Constant nt ty hty) -> return (P nt n ty)

lookupVal :: Name -> Context -> Maybe Value
lookupVal n ctxt 
   = do def <- lookupCtxt n ctxt
        case def of
          (Function (Fun _ _ _ htm)) -> return htm
          (Constant nt ty hty) -> return (VP nt n hty)

lookupTyEnv :: Name -> Env -> Maybe (Int, Type)
lookupTyEnv n env = li n 0 env where
  li n i []           = Nothing
  li n i ((x, b): xs) 
             | n == x = Just (i, binderTy b)
             | otherwise = li n (i+1) xs


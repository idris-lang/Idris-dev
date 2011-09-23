{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, DeriveFunctor #-}

module Core where

import Control.Monad.State
import Debug.Trace

{- The language has:
   * Full dependent types
   * A hierarchy of universes, with cumulativity: Set : Set1, Set1 : Set2, ...
   * Pattern matching letrec binding
   * (primitive types defined externally)

   Some technical stuff:
   * Typechecker is kept as simple as possible 
        - no unification, just a checker for incomplete terms.
   * We have a simple collection of tactics which we use to elaborate source
     programs with implicit syntax into fully explicit terms.
-}

data Option = SetInSet
            | CheckConv
  deriving Eq

-- RAW TERMS ----------------------------------------------------------------

-- Names are hierarchies of strings, describing scope (so no danger of
-- duplicate names, but need to be careful on lookup).
-- Also MN for machine chosen names

data Name = UN [String]
          | MN Int String
  deriving Eq

instance Show Name where
    show (UN [n]) = n
    show (UN (n:ns)) = show (UN [n]) ++ "." ++ show (UN ns)
    show (MN i s) = "{" ++ s ++ show i ++ "}"

data Raw = Var Name
         | RBind Name (Binder Raw) Raw
         | RApp Raw Raw
         | RSet Int
  deriving Show

data Binder b = Lam   { binderTy  :: b }
              | Pi    { binderTy  :: b }
              | Let   { binderTy  :: b,
                        binderVal :: b }
              | Hole  { binderTy  :: b}
              | Guess { binderTy  :: b,
                        binderVal :: b }
              | PVar  { binderTy  :: b }
  deriving (Show, Eq, Functor)

data RawFun = RawFun { rtype :: Raw,
                       rval  :: Raw
                     }
  deriving Show

data RDef = RFunction RawFun
          | RConst Raw
  deriving Show

type RProgram = [(Name, RDef)]

-- WELL TYPED TERMS ---------------------------------------------------------

data NameType = Ref | DCon Int Int | TCon Int
  deriving (Show, Eq)

data TT n = P NameType n (TT n) -- embed type
          | V Int 
          | Bind n (Binder (TT n)) (TT n)
          | App (TT n) (TT n) (TT n) -- function, function type, arg
          | Set Int
  deriving (Functor, Eq)

type EnvTT n = [(n, Binder (TT n))]

bindEnv :: EnvTT n -> TT n -> TT n
bindEnv [] tm = tm
bindEnv ((n, b):bs) tm = Bind n b (bindEnv bs tm)

type Term = TT Name
type Type = Term

type Env  = EnvTT Name

-- an environment with de Bruijn indices 'normalised' so that they all refer to
-- this environment

newtype WkEnvTT n = Wk (EnvTT n)
type WkEnv = WkEnvTT Name

instance Show n => Show (TT n) where
    show t = showEnv [] t
    
showEnv env t = showEnv' env t False
showEnvDbg env t = showEnv' env t True

showEnv' env t dbg = se 10 env t where
    se p env (P _ n _) = show n
    se p env (V i) | i < length env = (show $ fst $ env!!i) ++
                                      if dbg then "{" ++ show i ++ "}" else ""
                   | otherwise = "!!V " ++ show i ++ "!!"
    se p env (Bind n b sc) = bracket p 2 $ sb env n b ++ se 10 ((n,b):env) sc
    se p env (App f t a) = bracket p 1 $ se 1 env f ++ " " ++ se 0 env a
    se p env (Set i) = "Set" ++ show i

    sb env n (Lam t)  = showb env "\\ " " => " n t
    sb env n (Hole t) = showb env "? " ". " n t
    sb env n (Pi t)   = showb env "forall " " -> " n t
    sb env n (PVar t) = showb env "! " ". " n t
    sb env n (Let t v)   = showbv env "let " " in " n t v
    sb env n (Guess t v) = showbv env "?? " " in " n t v

    showb env op sc n t    = op ++ show n ++ " : " ++ se 10 env t ++ sc
    showbv env op sc n t v = op ++ show n ++ " : " ++ se 10 env t ++ " = " ++ 
                             se 10 env v ++ sc 

    bracket outer inner str | inner > outer = "(" ++ str ++ ")"
                            | otherwise = str

-- Check whether a term has any holes in it - impure if so

pureTerm :: TT n -> Bool
pureTerm (App f t a) = pureTerm f && pureTerm t && pureTerm a
pureTerm (Bind n b sc) = pureBinder b && pureTerm sc where
    pureBinder (Hole _) = False
    pureBinder (Guess _ _) = False
    pureBinder (Let t v) = pureTerm t && pureTerm v
    pureBinder t = pureTerm (binderTy t)
pureTerm _ = True

-- weaken a term by adding i to each de Bruijn index (i.e. lift it over i bindings)

weakenTm :: Int -> TT n -> TT n
weakenTm i t = wk i 0 t
  where wk i min (V x) | x >= min = V (i + x)
        wk i m (App f t a)   = App (wk i m f) (wk i m t) (wk i m a)
        wk i m (Bind x b sc) = Bind x (wkb i m b) (wk i (m + 1) sc)
        wk i m t = t
        wkb i m (Let   t v) = Let (wk i m t) (wk i m v)
        wkb i m (Guess t v) = Guess (wk i m t) (wk i m v)
        wkb i m t           = t { binderTy = wk i m (binderTy t) }

-- weaken an environment so that all the de Bruijn indices are correct according
-- to the latest bound variable

weakenEnv :: Show n => EnvTT n -> EnvTT n
weakenEnv env = wk (length env - 1) env
  where wk i [] = []
        wk i ((n, b) : bs) = (n, weakenTmB i b) : wk (i - 1) bs
        weakenTmB i (Let   t v) = Let (weakenTm i t) (weakenTm i v)
        weakenTmB i (Guess t v) = Guess (weakenTm i t) (weakenTm i v)
        weakenTmB i t           = t { binderTy = weakenTm i (binderTy t) }

-- WELL TYPED TERMS AS HOAS -------------------------------------------------

data HTT = HP NameType Name HTT
         | HV Int
         | HBind Name (Binder HTT) (HTT -> HTT)
         | HApp HTT HTT HTT
         | HSet Int
         | HTmp Int

instance Show HTT where
    show h = "<<HOAS>>"

hoas :: [HTT] -> TT Name -> HTT
hoas env (P nt n ty) = HP nt n (hoas env ty)
hoas env (V i) | i < length env = env!!i
               | otherwise = HV i
hoas env (Bind n b sc) = HBind n (hbind b) (\x -> hoas (x:env) sc)
  where hbind (Lam t)  = Lam (hoas env t)
        hbind (Pi t)   = Pi (hoas env t)
        hbind (Hole t) = Hole (hoas env t)
        hbind (PVar t) = PVar (hoas env t)
        hbind (Let v t)   = Let (hoas env v) (hoas env t)
        hbind (Guess v t) = Guess (hoas env v) (hoas env t)
hoas env (App f t a) = HApp (hoas env f) (hoas env t) (hoas env a)
hoas env (Set i) = HSet i

-- CONTEXTS -----------------------------------------------------------------

data Fun = Fun Type HTT Term HTT
  deriving Show

data Def = Function Fun
         | Constant NameType Type HTT
  deriving Show

type Context = [(Name, Def)]

emptyContext = []

addToCtxt :: Name -> Term -> Type -> Context -> Context
addToCtxt n tm ty ctxt = (n, Function (Fun ty (hoas [] ty)
                                           tm (hoas [] tm))) : ctxt

lookupTy :: Name -> Context -> Maybe Type
lookupTy n ctxt = do def <-  lookup n ctxt
                     case def of
                       (Function (Fun ty _ _ _)) -> return ty
                       (Constant _ ty _) -> return ty

lookupP :: Name -> Context -> Maybe Term
lookupP n ctxt 
   = do def <-  lookup n ctxt
        case def of
          (Function (Fun ty _ tm _)) -> return (P Ref n ty)
          (Constant nt ty hty) -> return (P nt n ty)

lookupVal :: Name -> Context -> Maybe HTT
lookupVal n ctxt 
   = do def <- lookup n ctxt
        case def of
          (Function (Fun _ _ _ htm)) -> return htm
          (Constant nt ty hty) -> return (HP nt n hty)

lookupTyEnv :: Name -> Env -> Maybe (Int, Type)
lookupTyEnv n env = li n 0 env where
  li n i []           = Nothing
  li n i ((x, b): xs) 
             | n == x = Just (i, binderTy b)
             | otherwise = li n (i+1) xs


x = UN ["x"]
xt = UN ["X"]
testtm = RBind xt (Lam (RSet 0)) (RBind x (Lam (Var xt)) (Var x))

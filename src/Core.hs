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

data TC a = OK a
          | Error String -- TMP! Make this an informative data structure
  deriving (Eq, Functor)

instance Show a => Show (TC a) where
    show (OK x) = show x
    show (Error str) = "Error: " ++ str

-- at some point, this instance should also carry type checking options
-- (e.g. Set:Set)

instance Monad TC where
    return = OK 
    x >>= k = case x of 
                OK v -> k v
                Error e -> Error e
    fail = Error

instance MonadPlus TC where
    mzero = Error "Unknown error"
    (OK x) `mplus` _ = OK x
    _ `mplus` (OK y) = OK y
    err `mplus` _    = err

-- RAW TERMS ----------------------------------------------------------------

-- Names are hierarchies of strings, describing scope (so no danger of
-- duplicate names, but need to be careful on lookup).
-- Also MN for machine chosen names

data Name = UN [String]
          | MN Int String
  deriving (Eq, Ord)

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
              | NLet  { binderTy  :: b,
                        binderVal :: b }
              | Hole  { binderTy  :: b}
              | Guess { binderTy  :: b,
                        binderVal :: b }
              | PVar  { binderTy  :: b }
  deriving (Show, Eq, Functor)

raw_apply :: Raw -> [Raw] -> Raw
raw_apply f [] = f
raw_apply f (a : as) = raw_apply (RApp f a) as

data RawFun = RawFun { rtype :: Raw,
                       rval  :: Raw
                     }
  deriving Show

data RawDatatype = RDatatype Name Raw [(Name, Raw)]
  deriving Show

data RDef = RFunction RawFun
          | RConst Raw
          | RData RawDatatype
  deriving Show

type RProgram = [(Name, RDef)]

-- WELL TYPED TERMS ---------------------------------------------------------

data NameType = Bound | Ref | DCon Int Int | TCon Int
  deriving (Show, Eq)

-- FIXME: Consider changing this to birectional, with type annotations.

data TT n = P NameType n (TT n) -- embed type
          | V Int 
          | Bind n (Binder (TT n)) (TT n)
          | App (TT n) (TT n) -- function, function type, arg
          | Set Int
  deriving Functor

type EnvTT n = [(n, Binder (TT n))]

data Datatype n = Data { d_typename :: n,
                         d_type     :: (TT n),
                         d_cons     :: [(n, TT n)] }
  deriving (Show, Functor, Eq)

instance Eq n => Eq (TT n) where
    (==) (P xt x _)     (P yt y _)     = xt == yt && x == y
    (==) (V x)          (V y)          = x == y
    (==) (Bind _ xb xs) (Bind _ yb ys) = xb == yb && xs == ys
    (==) (App fx ax)    (App fy ay)    = fx == fy && ax == ay
    (==) (Set x)        (Set y)        = x == y
    (==) _              _              = False

-- A few handy operations on well typed terms:

-- Returns true if V 0 and bound name n do not occur in the term

noOccurrence :: Eq n => n -> TT n -> Bool
noOccurrence n t = no' 0 t
  where
    no' i (V x) = not (i == x)
    no' i (P Bound x _) = not (n == x)
    no' i (Bind n b sc) = noB' i b && no' (i+1) sc
       where noB' i (Let t v) = no' i t && no' i v
             noB' i (Guess t v) = no' i t && no' i v
             noB' i b = no' i (binderTy b)
    no' i (App f a) = no' i f && no' i a
    no' i _ = True

-- Return the arity of a (normalised) type

arity :: TT n -> Int
arity (Bind n (Pi t) sc) = 1 + arity sc
arity _ = 0

-- deconstruct an application; returns the function and a list of arguments

unApply :: TT n -> (TT n, [TT n])
unApply t = ua [] t where
    ua args (App f a) = ua (a:args) f
    ua args t         = (t, reverse args)

forget :: TT Name -> Raw
forget tm = fe [] tm
  where
    fe env (P _ n _) = Var n
    fe env (V i)     = Var (env !! i)
    fe env (Bind n b sc) = RBind n (fmap (fe env) b) 
                                   (fe (n:env) sc)
    fe env (App f a) = RApp (fe env f) (fe env a)
    fe env (Set i)   = RSet i

type Term = TT Name
type Type = Term

type Env  = EnvTT Name

-- an environment with de Bruijn indices 'normalised' so that they all refer to
-- this environment

newtype WkEnvTT n = Wk (EnvTT n)
type WkEnv = WkEnvTT Name

instance (Eq n, Show n) => Show (TT n) where
    show t = showEnv [] t
    
showEnv env t = showEnv' env t False
showEnvDbg env t = showEnv' env t True

showEnv' env t dbg = se 10 env t where
    se p env (P nt n t) = show n 
                            ++ if dbg then "{" ++ show nt ++ " : " ++ se 10 env t ++ "}" else ""
    se p env (V i) | i < length env = (show $ fst $ env!!i) ++
                                      if dbg then "{" ++ show i ++ "}" else ""
                   | otherwise = "!!V " ++ show i ++ "!!"
    se p env (Bind n b@(Pi t) sc)  
        | noOccurrence n sc && not dbg = bracket p 2 $ se 10 env t ++ " -> " ++ se 10 ((n,b):env) sc
    se p env (Bind n b sc) = bracket p 2 $ sb env n b ++ se 10 ((n,b):env) sc
    se p env (App f a) = bracket p 1 $ se 1 env f ++ " " ++ se 0 env a
    se p env (Set i) = "Set" ++ show i

    sb env n (Lam t)  = showb env "\\ " " => " n t
    sb env n (Hole t) = showb env "? " ". " n t
    sb env n (Pi t)   = showb env "(" ") -> " n t
    sb env n (PVar t) = showb env "pat " ". " n t
    sb env n (Let t v)   = showbv env "let " " in " n t v
    sb env n (Guess t v) = showbv env "?? " " in " n t v

    showb env op sc n t    = op ++ show n ++ " : " ++ se 10 env t ++ sc
    showbv env op sc n t v = op ++ show n ++ " : " ++ se 10 env t ++ " = " ++ 
                             se 10 env v ++ sc 

    bracket outer inner str | inner > outer = "(" ++ str ++ ")"
                            | otherwise = str

-- Check whether a term has any holes in it - impure if so

pureTerm :: TT n -> Bool
pureTerm (App f a) = pureTerm f && pureTerm a
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
        wk i m (App f a)     = App (wk i m f) (wk i m a)
        wk i m (Bind x b sc) = Bind x (wkb i m b) (wk i (m + 1) sc)
        wk i m t = t
        wkb i m t           = fmap (wk i m) t

-- weaken an environment so that all the de Bruijn indices are correct according
-- to the latest bound variable

weakenEnv :: EnvTT n -> EnvTT n
weakenEnv env = wk (length env - 1) env
  where wk i [] = []
        wk i ((n, b) : bs) = (n, weakenTmB i b) : wk (i - 1) bs
        weakenTmB i (Let   t v) = Let (weakenTm i t) (weakenTm i v)
        weakenTmB i (Guess t v) = Guess (weakenTm i t) (weakenTm i v)
        weakenTmB i t           = t { binderTy = weakenTm i (binderTy t) }

weakenTmEnv :: Int -> EnvTT n -> EnvTT n
weakenTmEnv i = map (\ (n, b) -> (n, fmap (weakenTm i) b))



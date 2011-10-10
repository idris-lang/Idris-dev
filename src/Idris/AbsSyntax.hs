{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             TypeSynonymInstances #-}

module Idris.AbsSyntax where

import Core.TT
import Core.Evaluate

import Control.Monad.State
import Data.List
import Data.Char

data IOption = IOption { opt_logLevel :: Int }
    deriving (Show, Eq)

defaultOpts = IOption 0

-- TODO: Add 'module data' to IState, which can be saved out and reloaded quickly (i.e
-- without typechecking).
-- This will include all the functions and data declarations, plus fixity declarations
-- and syntax macros.

data IState = IState { tt_ctxt :: Context,
                       idris_infixes :: [FixDecl],
                       idris_implicits :: Ctxt ([Name], Int), -- implicits, arity
                       idris_log :: String,
                       idris_options :: IOption
                     }
                   
idrisInit = IState emptyContext [] emptyContext "" defaultOpts

-- The monad for the main REPL - reading and processing files and updating 
-- global state (hence the IO inner monad).
type Idris a = StateT IState IO a

getContext :: Idris Context
getContext = do i <- get; return (tt_ctxt i)

setContext :: Context -> Idris ()
setContext ctxt = do i <- get; put (i { tt_ctxt = ctxt } )

updateContext :: (Context -> Context) -> Idris ()
updateContext f = do i <- get; put (i { tt_ctxt = f (tt_ctxt i) } )

iputStrLn :: String -> Idris ()
iputStrLn = lift.putStrLn

tclift :: Show a => TC a -> Idris a
tclift tc = case tc of
               OK v -> return v
               err -> fail (show err)

setLogLevel :: Int -> Idris ()
setLogLevel l = do i <- get
                   let opts = idris_options i
                   let opt' = opts { opt_logLevel = l }
                   put (i { idris_options = opt' } )

logLevel :: Idris Int
logLevel = do i <- get
              return (opt_logLevel (idris_options i))

logLvl :: Int -> String -> Idris ()
logLvl l str = do i <- get
                  let lvl = opt_logLevel (idris_options i)
                  when (lvl >= l)
                      $ do lift (putStrLn str)
                           put (i { idris_log = idris_log i ++ str ++ "\n" } )

iLOG :: String -> Idris ()
iLOG = logLvl 1

-- Taken from the library source code - for ghc 6.12/7 compatibility
liftCatch :: (m (a,s) -> (e -> m (a,s)) -> m (a,s)) ->
    StateT s m a -> (e -> StateT s m a) -> StateT s m a
liftCatch catchError m h =
    StateT $ \s -> runStateT m s `catchError` \e -> runStateT (h e) s

idrisCatch :: Idris a -> (IOError -> Idris a) -> Idris a
idrisCatch op handler = liftCatch catch op handler

-- Commands in the REPL

data Command = Quit | Help | Eval PTerm 
             | TTShell 
             | NOP

-- Parsed declarations

data Fixity = Infixl { prec :: Int } 
            | Infixr { prec :: Int }
            | InfixN { prec :: Int } 
    deriving Eq

instance Show Fixity where
    show (Infixl i) = "infixl " ++ show i
    show (Infixr i) = "infixr " ++ show i
    show (InfixN i) = "infix " ++ show i

data FixDecl = Fix Fixity String 
    deriving (Show, Eq)

instance Ord FixDecl where
    compare (Fix x _) (Fix y _) = compare (prec x) (prec y)

data Plicity = Imp | Exp deriving Show

data PDecl' t = PFix     Fixity [String] -- fixity declaration
              | PTy      Name t          -- type declaration
              | PClauses Name [PClause' t]    -- pattern clause
              | PData    (PData' t)      -- data declaration
    deriving Functor

data PClause' t = PClause Name t t
    deriving Functor

data PData' t  = PDatadecl { d_name :: Name,
                             d_tcon :: t,
                             d_cons :: [(Name, t)] }
    deriving Functor

-- Handy to get a free function for applying PTerm -> PTerm functions
-- across a program, by deriving Functor

type PDecl   = PDecl' PTerm
type PData   = PData' PTerm
type PClause = PClause' PTerm
-- High level language terms

data PTerm = PQuote Raw
           | PRef Name
           | PLam Name PTerm PTerm
           | PPi  Plicity Name PTerm PTerm
           | PApp PTerm [(Name, PTerm)] [PTerm]
           | PHidden PTerm -- irrelevant or hidden pattern
           | PSet
           | Placeholder

--- Pretty printing declarations and terms

instance Show PTerm where
    show tm = showImp False tm

instance Show PDecl where
    show (PFix f ops) = show f ++ " " ++ showSep ", " ops
    show (PTy n ty) = show n ++ " : " ++ show ty
    show (PClauses n c) = showSep "\n" (map show c)
    show (PData d) = show d

instance Show PClause where
    show c = showCImp False c

instance Show PData where
    show d = showDImp False d

showCImp :: Bool -> PClause -> String
showCImp impl (PClause n l r) = showImp impl l ++ " = " ++ showImp impl r

showDImp :: Bool -> PData -> String
showDImp impl (PDatadecl n ty cons) 
   = "data " ++ show n ++ " : " ++ showImp impl ty ++ " where\n\t"
     ++ showSep "\n\t| " 
            (map (\ (n, t) -> show n ++ " : " ++ showImp impl t) cons)

showImp :: Bool -> PTerm -> String
showImp impl tm = se 10 tm where
    se p (PQuote r) = "![" ++ show r ++ "]"
    se p (PRef n) = show n
    se p (PLam n ty sc) = bracket p 2 $ "\\ " ++ show n ++ " => " ++ show sc
    se p (PPi Exp n ty sc)
        | n `elem` allNamesIn sc = bracket p 2 $
                                    "(" ++ show n ++ " : " ++ se 10 ty ++ 
                                    ") -> " ++ se 10 sc
        | otherwise = bracket p 2 $ se 10 ty ++ " -> " ++ se 10 sc
    se p (PPi Imp n ty sc)
        | impl = bracket p 2 $ "{" ++ show n ++ " : " ++ se 10 ty ++ 
                               "} -> " ++ se 10 sc
        | otherwise = se 10 sc
    se p (PApp (PRef f) _ [])
        | not impl = show f
    se p (PApp (PRef op@(UN [f:_])) _ [l, r])
        | not impl && not (isAlpha f) 
            = bracket p 1 $ se 1 l ++ " " ++ show op ++ " " ++ se 1 r
    se p (PApp f imps args) 
        = bracket p 1 $ se 1 f ++ (if impl then concatMap siArg imps else "")
                               ++ concatMap seArg args
    se p (PHidden tm) = "." ++ se 0 tm
    se p PSet = "Set"
    se p Placeholder = "_"

    seArg arg      = " " ++ se 0 arg
    siArg (n, val) = " {" ++ show n ++ " = " ++ se 10 val ++ "}"

    bracket outer inner str | inner > outer = "(" ++ str ++ ")"
                            | otherwise = str

allNamesIn :: PTerm -> [Name]
allNamesIn tm = nub $ ni [] tm 
  where
    ni env (PRef n)        
        | not (n `elem` env) = [n]
    ni env (PApp f is es)  = ni env f ++ concatMap (ni env) (map snd is) ++
                             concatMap (ni env) es
    ni env (PLam n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi _ n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PHidden tm)    = ni env tm
    ni env _               = []

namesIn :: IState -> PTerm -> [Name]
namesIn ist tm = nub $ ni [] tm 
  where
    ni env (PRef n)        
        | not (n `elem` env) 
            = case lookupCtxt n (idris_implicits ist) of
                Nothing -> [n]
                _ -> []
    ni env (PApp f is es)  = ni env f ++ concatMap (ni env) (map snd is) ++
                             concatMap (ni env) es
    ni env (PLam n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi _ n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PHidden tm)    = ni env tm
    ni env _               = []

-- For inferring types of things

inferTy   = MN 0 "__Infer"
inferCon  = MN 0 "__infer"
inferDecl = PDatadecl inferTy 
                      PSet
                      [(inferCon, PPi Imp (MN 0 "A") PSet (
                                  PPi Exp (MN 0 "a") (PRef (MN 0 "A"))
                                  (PRef inferTy)))]

infTerm t = PApp (PRef inferCon) [(MN 0 "A", Placeholder)] [t]
infP = P (TCon 0) inferTy (Set 0)

getInferTerm, getInferType :: Term -> Term
getInferTerm (Bind n b sc) = Bind n b $ getInferTerm sc
getInferTerm (App (App _ _) tm) = tm
getInferTerm tm = error ("getInferTerm " ++ show tm)

getInferType (Bind n b sc) = Bind n b $ getInferType sc
getInferType (App (App _ ty) _) = ty


-- Dealing with implicit arguments

-- Add implicit Pi bindings for any names in the term which appear in an
-- argument position.

implicitise :: IState -> PTerm -> (PTerm, ([Name], Int))
implicitise ist tm
    = let (declimps, a, ns) = execState (imps [] tm) ([], 0, []) in
          (pibind ns tm, (ns ++ reverse declimps, a))
  where
    imps env (PApp f is es)  
       = do (decls, a, ns) <- get
            let isn = concatMap (namesIn ist) (map snd is)
            let esn = concatMap (namesIn ist) es
            put (decls, a, nub (ns ++ ((isn ++ esn) \\ (env ++ decls))))
    imps env (PPi Imp n ty sc) 
        = do imps env ty
             (impdecls, a, ns) <- get
             put (n:impdecls, a, ns)
             imps (n:env) sc
    imps env (PPi Exp n ty sc) 
        = do imps env ty
             (impdecls, a, ns) <- get
             put (impdecls, a+1, ns)
             imps (n:env) sc
    imps env (PLam n ty sc)  
        = do imps env ty
             imps (n:env) sc
    imps env (PHidden tm)    = imps env tm
    imps env _               = return ()

    pibind []     sc = sc
    pibind (n:ns) sc = PPi Imp n Placeholder (pibind ns sc)

addImpl :: IState -> PTerm -> PTerm
addImpl ist ptm = ai [] ptm
  where
    ai env (PRef f)       = aiFn env (PRef f) [] []
    ai env (PApp (PRef f) is es) 
                          = let is' = map (\ (n, tm) -> (n, ai env tm)) is 
                                es' = map (ai env) es in
                                      aiFn env (PRef f) is' es'
    ai env (PApp f is es) = let f' = ai env f
                                is' = map (\ (n, tm) -> (n, ai env tm)) is 
                                es' = map (ai env) es in
                                      aiFn env f' is' es'
    ai env (PLam n ty sc) = let ty' = ai env ty
                                sc' = ai (n:env) sc in
                                PLam n ty' sc'
    ai env (PPi p n ty sc) = let ty' = ai env ty
                                 sc' = ai (n:env) sc in
                                 PPi p n ty' sc'
    ai env (PHidden tm) = PHidden (ai env tm)
    ai env tm = tm

    aiFn env (PRef f) is es | not (f `elem` env)
        = case lookupCtxt f (idris_implicits ist) of
            Just (ns, a) -> pApp a (PRef f) (insertImpl ns is) es
            Nothing      -> pApp 1 (PRef f) is es
    aiFn env f is es = pApp 1 f is es

    pApp a f [] [] = f
    pApp a f is es = let rest = drop a es in
                         appRest (PApp f is (take a es)) rest

    appRest f [] = f
    appRest f (a : as) = appRest (PApp f [] [a]) as

    insertImpl [] given = []
    insertImpl (n:ns) given 
        = case lookup n given of
            Just val -> (n, val) : insertImpl ns given
            Nothing  -> (n, Placeholder) : insertImpl ns given



{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.AbsSyntax where

import Core.TT
import Core.Evaluate

import Control.Monad.State
import Data.List

data IOption = Logging
    deriving (Show, Eq)

-- TODO: Add 'module data' to IState, which can be saved out and reloaded quickly (i.e
-- without typechecking).
-- This will include all the functions and data declarations, plus fixity declarations
-- and syntax macros.

data IState = IState { tt_ctxt :: Context,
                       idris_infixes :: [FixDecl],
                       idris_implicits :: Ctxt [Name],
                       idris_log :: String,
                       idris_options :: [IOption]
                     }
                   
idrisInit = IState emptyContext [] emptyContext "" []

-- The monad for the main REPL - reading and processing files and updating 
-- global state (hence the IO inner monad).
type Idris a = StateT IState IO a

iputStrLn :: String -> Idris ()
iputStrLn = lift.putStrLn

setOpt :: IOption -> Bool -> Idris ()
setOpt o True  = do i <- get
                    put (i { idris_options = nub (o : idris_options i) })
setOpt o False = do i <- get
                    put (i { idris_options = idris_options i \\ [o] })    

iLOG :: String -> Idris ()
iLOG str = do i <- get
              when (Logging `elem` idris_options i)
                   $ do lift (putStrLn str)
                        put (i { idris_log = idris_log i ++ str ++ "\n" } )

-- Commands in the REPL

data Command = Quit | Help | Eval PTerm 
             | NOP

-- Parsed declarations

data Fixity = Infixl { prec :: Int } 
            | Infixr { prec :: Int }
            | InfixN { prec :: Int } 
    deriving (Show, Eq)

data FixDecl = Fix Fixity String 
    deriving (Show, Eq)

instance Ord FixDecl where
    compare (Fix x _) (Fix y _) = compare (prec x) (prec y)

data Plicity = Imp | Exp deriving Show

data PDecl' t = PFix    Fixity [String] -- fixity declaration
              | PTy     Name   t        -- type declaration
              | PClause t      t        -- pattern clause
              | PData   (PData' t)      -- data declaration
    deriving (Show, Functor)

data PData' t  = PDatadecl { d_name :: Name,
                             d_tcon :: t,
                             d_cons :: [(Name, t)] }
    deriving (Show, Functor)

-- Handy to get a free function for applying PTerm -> PTerm functions
-- across a program, by deriving Functor

type PDecl = PDecl' PTerm
type PData = PData' PTerm

-- High level language terms

data PTerm = PQuote Raw
           | PRef Name
           | PLam Name PTerm PTerm
           | PPi  Plicity Name PTerm PTerm
           | PApp PTerm [(Name, PTerm)] [PTerm]
           | PHidden PTerm -- irrelevant or hidden pattern
           | PSet
           | Placeholder
    deriving Show

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

-- Dealing with implicit arguments

-- Add implicit Pi bindings for any names in the term which appear in an
-- argument position.

implicitise :: IState -> PTerm -> (PTerm, [Name])
implicitise ist tm
    = let (declimps, ns) = execState (imps [] tm) ([], []) in
          (pibind ns tm, ns ++ reverse declimps)
  where
    imps env (PApp f is es)  
       = do (decls, ns) <- get
            let isn = concatMap (namesIn ist) (map snd is)
            let esn = concatMap (namesIn ist) es
            put (decls, nub (ns ++ ((isn ++ esn) \\ env)))
    imps env (PPi Imp n ty sc) 
        = do imps env ty
             (decls, ns) <- get
             put (n:decls, ns)
             imps (n:env) sc
    imps env (PPi Exp n ty sc) 
        = do imps env ty
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
    ai env (PApp f is es) = let f' = ai env f
                                is' = map (\ (n, tm) -> (n, ai env tm)) is
                                es' = map (ai env) es in
                                      aiFn env f is' es'
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
            Just ns -> PApp (PRef f) (insertImpl ns is) es
            Nothing -> PApp (PRef f) is es
    aiFn env f is es = PApp f is es

    insertImpl [] given = []
    insertImpl (n:ns) given 
        = case lookup n given of
            Just val -> (n, val) : insertImpl ns given
            Nothing  -> (n, Placeholder) : insertImpl ns given



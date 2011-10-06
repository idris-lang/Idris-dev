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

-- Dealing with implicit arguments

implicitise :: IState -> PTerm -> (PTerm, [Name])
implicitise ist tm = (tm, [])

addImpl :: IState -> PTerm -> PTerm
addImpl ist ptm = ptm

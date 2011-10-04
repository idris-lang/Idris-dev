{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.AbsSyntax where

import Core.TT
import Core.Evaluate

import Control.Monad.State
import Data.List

data IOption = Logging
    deriving (Show, Eq)

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

data Command = Quit
             | Help

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

data PDecl = PFix    Fixity String   -- fixity declaration
           | PTy     Name   PTerm    -- type declaration
           | PClause PTerm  PTerm    -- pattern clause
           | PData   PData           -- data declaration
    deriving Show

data PData = PDatadecl { d_name :: Name,
                         d_tcon :: PTerm,
                         d_cons :: [(Name, PTerm)] }
    deriving Show

-- High level language terms

data PTerm = PQuote Raw
           | PRef Name
           | PLam Name PTerm PTerm
           | PPi  Plicity Name PTerm PTerm
           | PApp PTerm [(Name, PTerm)] [PTerm]
           | Placeholder
    deriving Show



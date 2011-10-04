{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.AbsSyntax where

import Core.TT
import Core.Evaluate

data IState = IState { tt_ctxt :: Context,
                       tt_infixes :: [FixDecl] 
                     }
                    
{- Plan:
   Treat it as a theorem prover - one definition at a time, parse, elaborate,
   and add to context. Since elaboration can be affected by definitions we've
   added (e.g.  plicity) -}

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



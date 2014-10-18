{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Transform where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.DSL
import Idris.Error
import Idris.Delaborate
import Idris.Imports
import Idris.ElabTerm
import Idris.Coverage
import Idris.DataOpts
import Idris.Providers
import Idris.Primitives
import Idris.Inliner
import Idris.PartialEval
import Idris.DeepSeq
import Idris.Output (iputStrLn, pshow, iWarn)
import IRTS.Lang

import Idris.Elab.Utils

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.Typecheck
import Idris.Core.CaseTree

import Idris.Docstrings

import Prelude hiding (id, (.))
import Control.Category

import Control.Applicative hiding (Const)
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict as State
import Data.List
import Data.Maybe
import Debug.Trace

import qualified Data.Map as Map
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Char(isLetter, toLower)
import Data.List.Split (splitOn)

import Util.Pretty(pretty, text)

elabTransform :: ElabInfo -> FC -> Bool -> PTerm -> PTerm -> Idris (Term, Term)
elabTransform info fc safe lhs_in@(PApp _ (PRef _ tf) _) rhs_in
    = do ctxt <- getContext
         i <- getIState
         let lhs = addImplPat i lhs_in
         ((lhs', dlhs, []), _) <-
              tclift $ elaborate ctxt (sMN 0 "transLHS") infP []
                       (erun fc (buildTC i info ELHS [] (sUN "transform")
                                   (infTerm lhs)))
         let lhs_tm = orderPats (getInferTerm lhs')
         let lhs_ty = getInferType lhs'
         let newargs = pvars i lhs_tm

         (clhs_tm, clhs_ty) <- recheckC fc [] lhs_tm
         logLvl 3 ("Transform LHS " ++ show clhs_tm)
         let rhs = addImplBound i (map fst newargs) rhs_in
         ((rhs', defer), _) <-
              tclift $ elaborate ctxt (sMN 0 "transRHS") clhs_ty []
                       (do pbinds i lhs_tm
                           setNextName
                           erun fc (build i info ERHS [] (sUN "transform") rhs)
                           erun fc $ psolve lhs_tm
                           tt <- get_term
                           return (runState (collectDeferred Nothing tt) []))
         (crhs_tm, crhs_ty) <- recheckC fc [] rhs'
         logLvl 3 ("Transform RHS " ++ show crhs_tm)
         -- Types must always convert
         case converts ctxt [] clhs_ty crhs_ty of
              OK _ -> return ()
              Error e -> ierror (At fc (CantUnify False clhs_tm crhs_tm e [] 0))
         -- In safe mode, values must convert (Thinks: This is probably not
         -- useful as is, perhaps it should require a proof of equality instead)
         when safe $ case converts ctxt [] clhs_tm crhs_tm of
              OK _ -> return ()
              Error e -> ierror (At fc (CantUnify False clhs_tm crhs_tm e [] 0))

         case unApply (depat clhs_tm) of
              (P _ tfname _, _) -> do addTrans tfname (clhs_tm, crhs_tm)
                                      addIBC (IBCTrans tf (clhs_tm, crhs_tm))
              _ -> ierror (At fc (Msg "Invalid transformation rule (must be function application)"))
         return (clhs_tm, crhs_tm)

  where
    depat (Bind n (PVar t) sc) = depat (instantiate (P Bound n t) sc)
    depat x = x

elabTransform info fc safe lhs_in rhs_in 
   = ierror (At fc (Msg "Invalid transformation rule (must be function application)"))

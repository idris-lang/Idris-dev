{-|
Module      : Idris.Elab.Transform
Description : Transformations for elaborate terms.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Transform where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.Core.CaseTree
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Coverage
import Idris.DataOpts
import Idris.DeepSeq
import Idris.Delaborate
import Idris.Docstrings
import Idris.DSL
import Idris.Elab.Term
import Idris.Elab.Utils
import Idris.Error
import Idris.Imports
import Idris.Inliner
import Idris.Output (iWarn, iputStrLn, pshow, sendHighlighting)
import Idris.PartialEval
import Idris.Primitives
import Idris.Providers
import IRTS.Lang

import Util.Pretty (pretty, text)

import Prelude hiding (id, (.))

import Control.Applicative hiding (Const)
import Control.Category
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict as State
import Data.Char (isLetter, toLower)
import Data.List
import Data.List.Split (splitOn)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Debug.Trace

elabTransform :: ElabInfo -> FC -> Bool -> PTerm -> PTerm -> Idris (Term, Term)
elabTransform info fc safe lhs_in@(PApp _ (PRef _ _ tf) _) rhs_in
    = do ctxt <- getContext
         i <- getIState
         let lhs = addImplPat i lhs_in
         logElab 5 ("Transform LHS input: " ++ showTmImpls lhs)
         (ElabResult lhs' dlhs [] ctxt' newDecls highlights newGName, _) <-
              tclift $ elaborate (constraintNS info) ctxt (idris_datatypes i) (idris_name i) (sMN 0 "transLHS") infP initEState
                       (erun fc (buildTC i info ETransLHS [] (sUN "transform")
                                   (allNamesIn lhs_in) (infTerm lhs)))
         setContext ctxt'
         processTacticDecls info newDecls
         sendHighlighting highlights
         updateIState $ \i -> i { idris_name = newGName }
         let lhs_tm = orderPats (getInferTerm lhs')
         let lhs_ty = getInferType lhs'
         let newargs = pvars i lhs_tm

         (clhs_tm_in, clhs_ty) <- recheckC_borrowing False False [] (constraintNS info) fc id [] lhs_tm
         let clhs_tm = renamepats pnames clhs_tm_in
         logElab 3 ("Transform LHS " ++ show clhs_tm)
         logElab 3 ("Transform type " ++ show clhs_ty)

         let rhs = addImplBound i (map fst newargs) rhs_in
         logElab 5 ("Transform RHS input: " ++ showTmImpls rhs)

         ((rhs', defer, ctxt', newDecls, newGName), _) <-
              tclift $ elaborate (constraintNS info) ctxt (idris_datatypes i) (idris_name i) (sMN 0 "transRHS") clhs_ty initEState
                       (do pbinds i lhs_tm
                           setNextName
                           (ElabResult _ _ _ ctxt' newDecls highlights newGName) <- erun fc (build i info ERHS [] (sUN "transform") rhs)
                           set_global_nextname newGName
                           erun fc $ psolve lhs_tm
                           tt <- get_term
                           let (rhs', defer) = runState (collectDeferred Nothing [] ctxt tt) []
                           newGName <- get_global_nextname
                           return (rhs', defer, ctxt', newDecls, newGName))
         setContext ctxt'
         processTacticDecls info newDecls
         sendHighlighting highlights
         updateIState $ \i -> i { idris_name = newGName }

         (crhs_tm_in, crhs_ty) <- recheckC_borrowing False False [] (constraintNS info) fc id [] rhs'
         let crhs_tm = renamepats pnames crhs_tm_in
         logElab 3 ("Transform RHS " ++ show crhs_tm)

         -- Types must always convert
         case converts ctxt [] clhs_ty crhs_ty of
              OK _ -> return ()
              Error e -> ierror (At fc (CantUnify False (clhs_tm, Nothing) (crhs_tm, Nothing) e [] 0))
         -- In safe mode, values must convert (Thinks: This is probably not
         -- useful as is, perhaps it should require a proof of equality instead)
         when safe $ case converts ctxt [] clhs_tm crhs_tm of
              OK _ -> return ()
              Error e -> ierror (At fc (CantUnify False (clhs_tm, Nothing) (crhs_tm, Nothing) e [] 0))

         case unApply (depat clhs_tm) of
              (P _ tfname _, _) -> do addTrans tfname (clhs_tm, crhs_tm)
                                      addIBC (IBCTrans tf (clhs_tm, crhs_tm))
              _ -> ierror (At fc (Msg "Invalid transformation rule (must be function application)"))
         return (clhs_tm, crhs_tm)

  where
    depat (Bind n (PVar _ t) sc) = depat (instantiate (P Bound n t) sc)
    depat x = x

    renamepats (n' : ns) (Bind n (PVar rig t) sc)
       = Bind n' (PVar rig t) (renamepats ns sc) -- all Vs
    renamepats _ sc = sc

    -- names for transformation variables. Need to ensure these don't clash
    -- with any other names when applying rules, so rename here.
    pnames = map (\i -> sMN i ("tvar" ++ show i)) [0..]

elabTransform info fc safe lhs_in rhs_in
   = ierror (At fc (Msg "Invalid transformation rule (must be function application)"))

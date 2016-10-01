{-|
Module      : Idris.Elab.Provider
Description : Code to elaborate type providers.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Provider(elabProvider) where

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
import Idris.Elab.Clause
import Idris.Elab.Term
import Idris.Elab.Type
import Idris.Elab.Utils
import Idris.Elab.Value
import Idris.Error
import Idris.Imports
import Idris.Inliner
import Idris.Output (iWarn, iputStrLn, pshow)
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

-- | Elaborate a type provider
elabProvider :: Docstring (Either Err PTerm) -> ElabInfo -> SyntaxInfo -> FC -> FC -> ProvideWhat -> Name -> Idris ()
elabProvider doc info syn fc nfc what n
    = do i <- getIState
         -- Ensure that the experimental extension is enabled
         unless (TypeProviders `elem` idris_language_extensions i) $
           ifail $ "Failed to define type provider \"" ++ show n ++
                   "\".\nYou must turn on the TypeProviders extension."

         ctxt <- getContext

         -- First elaborate the expected type (and check that it's a type)
         -- The goal type for a postulate is always Type.
         (ty', typ) <- case what of
                         ProvTerm ty p   -> elabVal info ERHS ty
                         ProvPostulate _ -> elabVal info ERHS (PType fc)
         unless (isTType typ) $
           ifail ("Expected a type, got " ++ show ty' ++ " : " ++ show typ)

         -- Elaborate the provider term to TT and check that the type matches
         (e, et) <- case what of
                      ProvTerm _ tm    -> elabVal info ERHS tm
                      ProvPostulate tm -> elabVal info ERHS tm
         unless (isProviderOf ctxt ty' et) $
           ifail $ "Expected provider type " ++ show (providerOf ty') ++
                   ", got " ++ show et ++ " instead."

         -- Execute the type provider and normalise the result
         -- use 'run__provider' to convert to a primitive IO action

         rhs <- execute (mkApp (P Ref (sUN "run__provider") Erased)
                                          [Erased, e])
         let rhs' = normalise ctxt [] rhs
         logElab 3 $ "Normalised " ++ show n ++ "'s RHS to " ++ show rhs

         -- Extract the provided term or postulate from the type provider
         provided <- getProvided fc rhs'

         case provided of
           Provide tm
             | ProvTerm ty _ <- what ->
               do -- Finally add a top-level definition of the provided term
                  elabType info syn doc [] fc [] n NoFC ty
                  elabClauses info fc [] n [PClause fc n (PApp fc (PRef fc [] n) []) [] (delab i tm) []]
                  logElab 3 $ "Elaborated provider " ++ show n ++ " as: " ++ show tm
             | ProvPostulate _ <- what ->
               do -- Add the postulate
                  elabPostulate info syn doc fc nfc [] n (delab i tm)
                  logElab 3 $ "Elaborated provided postulate " ++ show n
             | otherwise ->
               ierror . Msg $ "Attempted to provide a postulate where a term was expected."

    where isTType :: TT Name -> Bool
          isTType (TType _) = True
          isTType _ = False

          -- Note: IO (Providers.Provider ty) is used instead of IO'
          -- (MkFFI C_FFI) (Providers.Provider ty) in hopes of better
          -- error messages with less normalisation
          providerOf :: Type -> Type
          providerOf ty = App Complete (P Ref (sUN "IO") Erased) $
                            App Complete (P Ref (sNS (sUN "Provider") ["Providers", "Prelude"]) Erased)
                              ty

          isProviderOf :: Context -> TT Name -> TT Name -> Bool
          isProviderOf ctxt tp prov =
            case converts ctxt [] (providerOf tp) prov of
              OK _ -> True
              _    -> False

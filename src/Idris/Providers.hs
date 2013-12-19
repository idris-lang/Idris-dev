{-# LANGUAGE PatternGuards #-}
module Idris.Providers (providerTy, getProvided) where

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Error

import Debug.Trace

-- | Wrap a type provider in the type of type providers
providerTy :: FC -> PTerm -> PTerm
providerTy fc tm = PApp fc (PRef fc $ UN "Provider") [PExp 0 False tm ""]

-- | Handle an error, if the type provider returned an error. Otherwise return the provided term.
getProvided :: TT Name -> Idris (TT Name)
getProvided tm | (P _ (UN "prim_io_return") _, [tp, result]) <- unApply tm
               , (P _ (NS (UN "Error") ["Providers"]) _, [_, err]) <- unApply result =
                     case err of
                       Constant (Str msg) -> ierror . ProviderError $ msg
                       _ -> ifail "Internal error in type provider, non-normalised error"
               | (P _ (UN "prim_io_return") _, [tp, result]) <- unApply tm
               , (P _ (NS (UN "Provide") ["Providers"]) _, [_, res]) <- unApply result =
                     return res
               | otherwise = ifail $ "Internal type provider error: result was not " ++
                                     "IO (Provider a), or perhaps missing normalisation."

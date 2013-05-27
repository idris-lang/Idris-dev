{-# LANGUAGE PatternGuards #-}
module Idris.Providers (providerTy, getProvided) where

import Core.TT
import Core.Evaluate
import Core.Execute
import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Error

import Debug.Trace

-- | Wrap a type provider in the type of type providers
providerTy :: FC -> PTerm -> PTerm
providerTy fc tm = PApp fc (PRef fc $ UN "Provider") [PExp 0 False tm ""]

-- | Handle an error, if the type provider returned an error. Otherwise return the provided term.
getProvided :: TT Name -> Idris (TT Name)
getProvided tm | (P _ (UN "io_return") _, [tp, result]) <- unApply tm
               , (P _ (NS (UN "Error") ["Providers"]) _, [_, err]) <- unApply result =
                     case err of
                       Constant (Str msg) -> ierror . ProviderError $ msg
                       _ -> fail "Internal error in type provider, non-normalised error"
               | (P _ (UN "io_return") _, [tp, result]) <- unApply tm
               , (P _ (NS (UN "Provide") ["Providers"]) _, [_, res]) <- unApply result =
                     return res
               | otherwise = fail $ "Internal type provider error: result was not " ++
                                    "IO (Provider a), or perhaps missing normalisation."

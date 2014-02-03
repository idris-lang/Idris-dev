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
providerTy fc tm = PApp fc (PRef fc $ sUN "Provider") [PExp 0 [] tm ""]

ioret = sUN "prim_io_return"
ermod = sNS (sUN "Error") ["Providers"]
prmod = sNS (sUN "Provide") ["Providers"]

-- | Handle an error, if the type provider returned an error. Otherwise return the provided term.
getProvided :: FC -> TT Name -> Idris (TT Name)
getProvided fc tm | (P _ pioret _, [tp, result]) <- unApply tm
                  , (P _ nm _, [_, err]) <- unApply result 
                  , pioret == ioret && nm == ermod
                      = case err of
                          Constant (Str msg) -> ierror . At fc . ProviderError $ msg
                          _ -> ifail "Internal error in type provider, non-normalised error"
                  | (P _ pioret _, [tp, result]) <- unApply tm
                  , (P _ nm _, [_, res]) <- unApply result 
                  , pioret == ioret && nm == prmod
                      = return res
                  | otherwise = ifail $ "Internal type provider error: result was not " ++
                                        "IO (Provider a), or perhaps missing normalisation."


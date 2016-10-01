{-|
Module      : Idris.Providers
Description : Idris' 'Type Provider' implementation.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE DeriveFunctor, PatternGuards #-}
module Idris.Providers (
    providerTy
  , getProvided
  , Provided(..)
  ) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Error

-- | Wrap a type provider in the type of type providers
providerTy :: FC -> PTerm -> PTerm
providerTy fc tm
  = PApp fc (PRef fc [] $ sNS (sUN "Provider" ) ["Providers", "Prelude"]) [PExp 0 [] (sMN 0 "pvarg") tm]

ioret :: Name
ioret = sUN "prim_io_pure"

ermod :: Name
ermod = sNS (sUN "Error") ["Providers", "Prelude"]

prmod :: Name
prmod = sNS (sUN "Provide") ["Providers", "Prelude"]

data Provided a = Provide a
  deriving (Show, Eq, Functor)

-- | Handle an error, if the type provider returned an error. Otherwise return the provided term.
getProvided :: FC -> TT Name -> Idris (Provided (TT Name))
getProvided fc tm | (P _ pioret _, [tp, result]) <- unApply tm
                  , (P _ nm _, [_, err]) <- unApply result
                  , pioret == ioret && nm == ermod
                      = case err of
                          Constant (Str msg) -> ierror . At fc . ProviderError $ msg
                          _ -> ifail "Internal error in type provider, non-normalised error"
                  | (P _ pioret _, [tp, result]) <- unApply tm
                  , (P _ nm _, [_, res]) <- unApply result
                  , pioret == ioret && nm == prmod
                      = return . Provide $ res
                  | otherwise = ifail $ "Internal type provider error: result was not " ++
                                        "IO (Provider a), or perhaps missing normalisation.\n" ++
                                        "Term: " ++ take 1000 (show tm)

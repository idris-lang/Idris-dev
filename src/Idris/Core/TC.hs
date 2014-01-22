{-# LANGUAGE DeriveFunctor #-}

module Idris.Core.TC(TC'(..)) where

import Control.Monad
import Control.Monad.Trans.Error(Error(..))

data TC' e a = OK !a
             | Error e
  deriving (Eq, Functor)

bindTC :: TC' e a -> (a -> TC' e b) -> TC' e b
bindTC x k = case x of
                OK v -> k v
                Error e -> Error e
{-# INLINE bindTC #-}

instance Error e => Monad (TC' e) where
    return x = OK x
    x >>= k = bindTC x k 
    fail e = Error (strMsg e)

instance Error e => MonadPlus (TC' e) where
    mzero = fail "Unknown error"
    (OK x) `mplus` _ = OK x
    _ `mplus` (OK y) = OK y
    err `mplus` _    = err


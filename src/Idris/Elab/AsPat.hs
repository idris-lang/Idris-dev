{-|
Module      : Idris.Elab.AsPat
Description : Code to elaborate pattern variables.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Elab.AsPat(desugarAs) where

import Idris.AbsSyntax
import Idris.Core.TT

import Control.Applicative
import Control.Monad.State.Strict
import Data.Generics.Uniplate.Data (transformM)

-- | Desugar by changing x@y on lhs to let x = y in ... or rhs
desugarAs :: PTerm -> PTerm -> (PTerm, PTerm)
desugarAs lhs rhs
    = let (lhs', pats) = runState (collectAs (replaceUnderscore lhs)) [] in
          (lhs', bindPats pats rhs)
  where
    bindPats :: [(Name, FC, PTerm)] -> PTerm -> PTerm
    bindPats [] rhs = rhs
    bindPats ((n, fc, tm) : ps) rhs
       = PLet fc n NoFC Placeholder tm (bindPats ps rhs)

collectAs :: PTerm -> State [(Name, FC, PTerm)] PTerm
collectAs (PAs fc n tm) = do tm' <- collectAs tm
                             pats <- get
                             put (pats ++ [(n, fc, tm')])
                             return tm'
collectAs (PApp fc t as)
    = do as_tm <- mapM collectAs (map getTm as)
         let as' = zipWith (\a tm -> a { getTm = tm }) as as_tm
         return (PApp fc t as') -- only valid on args
-- only for 'ExactlyOne' since it means the alternatives will have the
-- same form, so we can assume we only need to extract from the first one
collectAs tm@(PAlternative ns (ExactlyOne d) (a : as))
    = do a' <- collectAs a
         pats <- get
         as' <- mapM collectAs as -- just to drop the '@'
         put pats -- discard later ones, since they're repeated
         return (PAlternative ns (ExactlyOne d) (a' : as'))
collectAs x = return x

-- | Replace _-patterns under @-patterns with fresh names that can be
-- used on the RHS
replaceUnderscore :: PTerm -> PTerm
replaceUnderscore tm = evalState (transformM (underAs replaceUnderscore') tm) 0
  where
    underAs :: (PTerm -> State Int PTerm) -> PTerm -> State Int PTerm
    underAs f (PAs fc n tm) = PAs fc n <$> transformM f tm
    underAs f x = return x

    fresh :: State Int Name
    fresh = modify (+1) >> flip sMN "underscorePatVar" <$> get


    replaceUnderscore' :: PTerm -> State Int PTerm
    replaceUnderscore' Placeholder = PRef emptyFC [] <$> fresh
    replaceUnderscore' tm          = return tm

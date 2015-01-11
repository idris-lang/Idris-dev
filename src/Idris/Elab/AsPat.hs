module Idris.Elab.AsPat(desugarAs) where

import Idris.Core.TT
import Idris.AbsSyntax

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
       = PLet fc n Placeholder tm (bindPats ps rhs)

collectAs :: PTerm -> State [(Name, FC, PTerm)] PTerm
collectAs (PAs fc n tm) = do tm' <- collectAs tm
                             pats <- get
                             put (pats ++ [(n, fc, tm')])
                             return tm'
collectAs (PApp fc t as)
    = do as_tm <- mapM collectAs (map getTm as)
         let as' = zipWith (\a tm -> a { getTm = tm }) as as_tm
         return (PApp fc t as') -- only valid on args
collectAs x = return x

-- | Replace _-patterns under @-patterns with fresh names that can be
-- used on the RHS
replaceUnderscore :: PTerm -> PTerm
replaceUnderscore tm = evalState (transformM replaceUnderscore' tm) 0
  where
    fresh :: State Int Name
    fresh = flip sMN "underscorePatVar" <$> get
    replaceUnderscore' :: PTerm -> State Int PTerm
    replaceUnderscore' Placeholder = PRef emptyFC <$> fresh
    replaceUnderscore' tm          = return tm

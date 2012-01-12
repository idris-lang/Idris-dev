{-# LANGUAGE PatternGuards #-}

module Idris.Transforms where

import Idris.AbsSyntax
import Core.CaseTree
import Core.TT

class Transform a where
    transform :: (a -> a) -> a -> a

instance Transform (TT Name) where
    transform t x = t (trans' x) where
        trans' (Bind n b sc) = Bind n (fmap (transform t) b) (transform t sc)
        trans' (App f a) = App (transform t f) (transform t a)
        trans' x = x

type TTOpt = TT Name -> TT Name

optimisations :: [TTOpt]
optimisations = [zero, suc]

instance Transform SC where
    transform t x = t (trans' x) where
        trans' (Case n alts) = Case n (map transAlt alts)
        trans' t = t

        transAlt (ConCase n i as sc) = ConCase n i as (trans' sc)
        transAlt (ConstCase c sc) = ConstCase c (trans' sc)
        transAlt (DefaultCase sc) = DefaultCase (trans' sc)

type CaseOpt = SC -> SC

zero :: TTOpt
zero (P _ n _) | n == NS (UN "O") ["nat","prelude"] 
    = Constant (BI 0)
zero x = x

suc :: TTOpt
suc (App (P _ s _) a) | s == NS (UN "S") ["nat","prelude"] 
    = mkApp (P Ref (UN "prim__addBigInt") Erased) [Constant (BI 1), a]
suc x = x



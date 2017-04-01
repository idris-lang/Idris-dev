{-|
Module      : Idris.DataOpts
Description : Optimisations for Idris code i.e. Forcing, detagging and collapsing.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}

module Idris.DataOpts(applyOpts) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Core.TT

import Control.Applicative
import Data.List
import Data.Maybe
import Debug.Trace

class Optimisable term where
    applyOpts :: term -> Idris term

instance (Optimisable a, Optimisable b) => Optimisable (a, b) where
    applyOpts (x, y) = (,) <$> applyOpts x <*> applyOpts y

instance (Optimisable a, Optimisable b) => Optimisable (vs, a, b) where
    applyOpts (v, x, y) = (,,) v <$> applyOpts x <*> applyOpts y

instance Optimisable a => Optimisable [a] where
    applyOpts = mapM applyOpts

instance Optimisable a => Optimisable (Either a (a, a)) where
    applyOpts (Left  t) = Left  <$> applyOpts t
    applyOpts (Right t) = Right <$> applyOpts t

-- Raw is for compile time optimisation (before type checking)
-- Term is for run time optimisation (after type checking, collapsing allowed)
-- Compile time: no collapsing

instance Optimisable Raw where
    applyOpts t@(RApp f a)
        | (Var n, args) <- raw_unapply t -- MAGIC HERE
            = raw_apply (Var n) <$> mapM applyOpts args
        | otherwise = RApp <$> applyOpts f <*> applyOpts a

    applyOpts (RBind n b t) = RBind n <$> applyOpts b <*> applyOpts t
    applyOpts t = return t

-- Erase types (makes ibc smaller, and we don't need them)
instance Optimisable (Binder (TT Name)) where
    applyOpts (Let t v) = Let <$> return Erased <*> applyOpts v
    applyOpts b = return (b { binderTy = Erased })

instance Optimisable (Binder Raw) where
    applyOpts b = do t' <- applyOpts (binderTy b)
                     return (b { binderTy = t' })

-- Run-time: do everything

prel = [txt "Nat", txt "Prelude"]

instance Optimisable (TT Name) where
    applyOpts (P _ (NS (UN fn) mod) _)
       | fn == txt "plus" && mod == prel
        = return (P Ref (sUN "prim__addBigInt") Erased)
    applyOpts (P _ (NS (UN fn) mod) _)
       | fn == txt "mult" && mod == prel
        = return (P Ref (sUN "prim__mulBigInt") Erased)
    applyOpts (P _ (NS (UN fn) mod) _)
       | fn == txt "divNat" && mod == prel
        = return (P Ref (sUN "prim__sdivBigInt") Erased)
    applyOpts (P _ (NS (UN fn) mod) _)
       | fn == txt "modNat" && mod == prel
        = return (P Ref (sUN "prim__sremBigInt") Erased)
    applyOpts (App _ (P _ (NS (UN fn) mod) _) x)
       | fn == txt "fromIntegerNat" && mod == prel
        = applyOpts x
    applyOpts (P _ (NS (UN fn) mod) _)
       | fn == txt "fromIntegerNat" && mod == prel
        = return (App Complete (P Ref (sNS (sUN "id") ["Basics","Prelude"]) Erased) Erased)
    applyOpts (P _ (NS (UN fn) mod) _)
       | fn == txt "toIntegerNat" && mod == prel
         = return (App Complete (P Ref (sNS (sUN "id") ["Basics","Prelude"]) Erased) Erased)
    applyOpts c@(P (DCon t arity uniq) n _)
        = return $ applyDataOptRT n t arity uniq []
    applyOpts t@(App s f a)
        | (c@(P (DCon t arity uniq) n _), args) <- unApply t
            = applyDataOptRT n t arity uniq <$> mapM applyOpts args
        | otherwise = App s <$> applyOpts f <*> applyOpts a
    applyOpts (Bind n b t) = Bind n <$> applyOpts b <*> applyOpts t
    applyOpts (Proj t i) = Proj <$> applyOpts t <*> pure i
    applyOpts t = return t

-- | Need to saturate arguments first to ensure that optimisation happens uniformly
applyDataOptRT :: Name -> Int -> Int -> Bool -> [Term] -> Term
applyDataOptRT n tag arity uniq args
    | length args == arity = doOpts n args
    | otherwise = let extra = satArgs (arity - length args)
                      tm = doOpts n (map (weakenTm (length extra)) args ++ map (\n -> P Bound n Erased) extra)
                  in bind extra tm
  where
    satArgs n = map (\i -> sMN i "sat") [1..n]

    bind [] tm = tm
    bind (n:ns) tm = Bind n (Lam RigW Erased) (pToV n (bind ns tm))

    -- Nat special cases
    -- TODO: Would be nice if this was configurable in idris source!
    -- Issue #1597 https://github.com/idris-lang/Idris-dev/issues/1597
    doOpts (NS (UN z) [nat, prelude]) []
        | z == txt "Z" && nat == txt "Nat" && prelude == txt "Prelude"
          = Constant (BI 0)
    doOpts (NS (UN s) [nat, prelude]) [k]
        | s == txt "S" && nat == txt "Nat" && prelude == txt "Prelude"
          = App Complete (App Complete (P Ref (sUN "prim__addBigInt") Erased) k) (Constant (BI 1))

    doOpts n args = mkApp (P (DCon tag arity uniq) n Erased) args

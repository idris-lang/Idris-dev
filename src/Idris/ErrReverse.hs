{-|
Module      : Idris.ErrReverse
Description : Utility to make errors readable using transformations.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}

module Idris.ErrReverse(errReverse) where

import Idris.AbsSyntax
import Idris.Core.Evaluate (unfold)
import Idris.Core.TT
import Util.Pretty

import Data.List
import Debug.Trace

-- | For display purposes, apply any 'error reversal' transformations
-- so that errors will be more readable,
-- and any 'error reduce' transformations
errReverse :: IState -> Term -> Term
errReverse ist t = rewrite 5 (do_unfold t) -- (elideLambdas t)
  where
    do_unfold :: Term -> Term
    do_unfold t = let ns = idris_errReduce ist in
                      if null ns then t
                         else unfold (tt_ctxt ist) []
                                     (map (\x -> (x, 1000)) (idris_errReduce ist))
                                     t

    rewrite 0 t = t
    rewrite n t = let t' = foldl applyRule t (reverse (idris_errRev ist)) in
                      if t == t' then t
                                 else rewrite (n - 1) t'

    applyRule :: Term -> (Term, Term) -> Term
    applyRule t (l, r) = applyNames [] t l r

    -- Assume pattern bindings match in l and r (if they don't just treat
    -- the rule as invalid and return t)

    applyNames ns t (Bind n (PVar _ ty) scl) (Bind n' (PVar _ ty') scr)
       | n == n' = applyNames (n : ns) t (instantiate (P Ref n ty) scl)
                                         (instantiate (P Ref n' ty') scr)
       | otherwise = t
    applyNames ns t l r = matchTerm ns l r t

    matchTerm ns l r t
       | Just nmap <- match ns l t = substNames nmap r
    matchTerm ns l r (App s f a) = let f' = matchTerm ns l r f
                                       a' = matchTerm ns l r a in
                                       App s f' a'
    matchTerm ns l r (Bind n b sc) = let b' = fmap (matchTerm ns l r) b
                                         sc' = matchTerm ns l r sc in
                                         Bind n b' sc'
    matchTerm ns l r t = t

    match ns l t = do ms <- match' ns l t
                      combine (nub ms)

    -- If any duplicate mappings, it's a failure
    combine [] = Just []
    combine ((x, t) : xs)
       | Just _ <- lookup x xs = Nothing
       | otherwise = do xs' <- combine xs
                        Just ((x, t) : xs')

    match' ns (P Ref n _) t | n `elem` ns = Just [(n, t)]
    match' ns (App _ f a) (App _ f' a') = do fs <- match' ns f f'
                                             as <- match' ns a a'
                                             Just (fs ++ as)
    -- no matching Binds, for now...
    match' ns x y = if x == y then Just [] else Nothing

    -- if the term under a lambda is huge, there's no much point in showing
    -- it as it won't be very enlightening.

    elideLambdas (App s f a) = App s (elideLambdas f) (elideLambdas a)
    elideLambdas (Bind n (Lam _ t) sc)
       | size sc > 200 = P Ref (sUN "...") Erased
    elideLambdas (Bind n b sc)
       = Bind n (fmap elideLambdas b) (elideLambdas sc)
    elideLambdas t = t

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, PatternGuards #-}

{- Implements a proof state, some primitive tactics for manipulating
   proofs, and some high level commands for introducing new theorems,
   evaluation/checking inside the proof system, etc. --}

module Idris.Core.ProofTerm(ProofTerm, Goal(..), mkProofTerm, getProofTerm,
                            updateSolved, updateSolvedTerm, 
                            bound_in, bound_in_term,
                            Hole, RunTactic',
                            goal, atHole) where

import Idris.Core.Typecheck
import Idris.Core.Evaluate
import Idris.Core.TT

import Control.Monad.State.Strict
import Data.List
import Debug.Trace

newtype ProofTerm = PT Term

type RunTactic' a = Context -> Env -> Term -> StateT a TC Term
type Hole = Maybe Name -- Nothing = default hole, first in list in proof state

data Goal = GD { premises :: Env,
                 goalType :: Binder Term
               }

mkProofTerm :: Term -> ProofTerm
mkProofTerm tm = PT tm

getProofTerm :: ProofTerm -> Term
getProofTerm (PT tm) = tm

same Nothing n  = True
same (Just x) n = x == n

hole (Hole _)    = True
hole (Guess _ _) = True
hole _           = False

updateSolvedTerm :: [(Name, Term)] -> Term -> Term 
updateSolvedTerm xs x = updateSolved' xs x where
    updateSolved' [] x = x
    updateSolved' xs (Bind n (Hole ty) t)
        | Just v <- lookup n xs 
            = case xs of
                   [_] -> substV v $ psubst n v t -- some may be Vs! Can't assume
                                                  -- explicit names
                   _ -> substV v $ psubst n v (updateSolved' xs t)
    updateSolved' xs (Bind n b t)
        | otherwise = Bind n (fmap (updateSolved' xs) b) (updateSolved' xs t)
    updateSolved' xs (App f a) 
        = App (updateSolved' xs f) (updateSolved' xs a)
    updateSolved' xs (P _ n@(MN _ _) _)
        | Just v <- lookup n xs = v
    updateSolved' xs t = t

updateSolved :: [(Name, Term)] -> ProofTerm -> ProofTerm 
updateSolved xs (PT x) = PT (updateSolvedTerm xs x) 

goal :: Hole -> ProofTerm -> TC Goal
goal h (PT tm) = g [] tm where
    g env (Bind n b@(Guess _ _) sc)
                        | same h n = return $ GD env b
                        | otherwise
                           = gb env b `mplus` g ((n, b):env) sc
    g env (Bind n b sc) | hole b && same h n = return $ GD env b
                        | otherwise
                           = g ((n, b):env) sc `mplus` gb env b
    g env (App f a)   = g env f `mplus` g env a
    g env t           = fail "Can't find hole"

    gb env (Let t v) = g env v `mplus` g env t
    gb env (Guess t v) = g env v `mplus` g env t
    gb env t = g env (binderTy t)

atHole :: Hole -> RunTactic' a -> Context -> Env -> ProofTerm -> 
          StateT a TC (ProofTerm, Bool)
atHole h f c e (PT t) = do (tm, u) <- atH f c e t 
                           return (PT tm, u)
  where
    updated o = do o' <- o
                   return (o', True)

    ulift2 f c env op a b
                  = do (b', u) <- atH f c env b
                       if u then return (op a b', True)
                            else do (a', u) <- atH f c env a
                                    return (op a' b', u)

    -- Search the things most likely to contain the binding first!

    atH :: RunTactic' a -> Context -> Env -> Term -> StateT a TC (Term, Bool)
    atH f c env binder@(Bind n b@(Guess t v) sc)
        | same h n = updated (f c env binder)
        | otherwise
            = do -- binder first
                 (b', u) <- ulift2 f c env Guess t v
                 if u then return (Bind n b' sc, True)
                      else do (sc', u) <- atH f c ((n, b) : env) sc
                              return (Bind n b' sc', u)
    atH f c env binder@(Bind n b sc)
        | hole b && same h n = updated (f c env binder)
        | otherwise -- scope first
            = do (sc', u) <- atH f c ((n, b) : env) sc
                 if u then return (Bind n b sc', True)
                      else do (b', u) <- atHb f c env b
                              return (Bind n b' sc', u)
    atH tac c env (App f a)    = ulift2 tac c env App f a
    atH tac c env t            = return (t, False)

    atHb f c env (Let t v)   = ulift2 f c env Let t v
    atHb f c env (Guess t v) = ulift2 f c env Guess t v
    atHb f c env t           = do (ty', u) <- atH f c env (binderTy t)
                                  return (t { binderTy = ty' }, u)

bound_in :: ProofTerm -> [Name]
bound_in (PT tm) = bound_in_term tm

bound_in_term :: Term -> [Name]
bound_in_term (Bind n b sc) = n : bi b ++ bound_in_term sc
  where
    bi (Let t v) = bound_in_term t ++ bound_in_term v
    bi (Guess t v) = bound_in_term t ++ bound_in_term v
    bi b = bound_in_term (binderTy b)
bound_in_term (App f a) = bound_in_term f ++ bound_in_term a
bound_in_term _ = []


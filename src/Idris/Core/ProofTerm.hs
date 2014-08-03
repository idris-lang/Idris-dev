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

data TermPath = Top
              | AppL TermPath Term
              | AppR Term TermPath
              | InBind Name BinderPath Term
              | InScope Name (Binder Term) TermPath
  deriving Show

data BinderPath = Binder (Binder TermPath)
                | LetT TermPath Term
                | LetV Term TermPath
                | GuessT TermPath Term
                | GuessV Term TermPath
  deriving Show

replaceTop :: TermPath -> TermPath -> TermPath
replaceTop p Top = p
replaceTop p (AppL l t) = AppL (replaceTop p l) t
replaceTop p (AppR t r) = AppR t (replaceTop p r)
replaceTop p (InBind n bp sc) = InBind n (replaceTopB p bp) sc
  where
    replaceTopB p (Binder b) = Binder (fmap (replaceTop p) b)
    replaceTopB p (LetT t v) = LetT (replaceTop p t) v
    replaceTopB p (LetV t v) = LetV t (replaceTop p v)
    replaceTopB p (GuessT t v) = GuessT (replaceTop p t) v
    replaceTopB p (GuessV t v) = GuessV t (replaceTop p v)
replaceTop p (InScope n b sc) = InScope n b (replaceTop p sc)

rebuildTerm :: Term -> TermPath -> Term
rebuildTerm tm Top = tm
rebuildTerm tm (AppL p a) = App (rebuildTerm tm p) a
rebuildTerm tm (AppR f p) = App f (rebuildTerm tm p)
rebuildTerm tm (InScope n b p) = Bind n b (rebuildTerm tm p)
rebuildTerm tm (InBind n bp sc) = Bind n (rebuildBinder tm bp) sc

rebuildBinder :: Term -> BinderPath -> Binder Term
rebuildBinder tm (Binder p) = fmap (rebuildTerm tm) p
rebuildBinder tm (LetT p t) = Let (rebuildTerm tm p) t
rebuildBinder tm (LetV v p) = Let v (rebuildTerm tm p)
rebuildBinder tm (GuessT p t) = Guess (rebuildTerm tm p) t
rebuildBinder tm (GuessV v p) = Guess v (rebuildTerm tm p)

findHole :: Name -> Env -> Term -> Maybe (TermPath, Env, Term)
findHole n env t = fh' env Top t where
  fh' env path tm@(Bind x h sc) 
      | hole h && n == x = Just (path, env, tm)
  fh' env path (App f a)
      | Just (p, env', tm) <- fh' env path f = Just (AppL p a, env', tm)
      | Just (p, env', tm) <- fh' env path a = Just (AppR f p, env', tm)
  fh' env path (Bind x b sc)
      | Just (bp, env', tm) <- fhB env path b = Just (InBind x bp sc, env', tm)
      | Just (p, env', tm) <- fh' ((x,b):env) path sc = Just (InScope x b p, env', tm)
  fh' _ _ _ = Nothing

  fhB env path (Let t v)
      | Just (p, env', tm) <- fh' env path t = Just (LetT p v, env', tm)
      | Just (p, env', tm) <- fh' env path v = Just (LetV t p, env', tm)
  fhB env path (Guess t v)
      | Just (p, env', tm) <- fh' env path t = Just (GuessT p v, env', tm)
      | Just (p, env', tm) <- fh' env path v = Just (GuessV t p, env', tm)
  fhB env path b
      | Just (p, env', tm) <- fh' env path (binderTy b)
          = Just (Binder (fmap (\_ -> p) b), env', tm)
  fhB _ _ _ = Nothing 

data ProofTerm = PT { -- wholeterm :: Term,
                      path :: TermPath,
                      subterm_env :: Env,
                      subterm :: Term }
  deriving Show

type RunTactic' a = Context -> Env -> Term -> StateT a TC Term
type Hole = Maybe Name -- Nothing = default hole, first in list in proof state

refocus :: Hole -> ProofTerm -> ProofTerm
refocus h t = let res = refocus' h t in res
--                   trace ("OLD: " ++ show t ++ "\n" ++
--                          "REFOCUSSED " ++ show h ++ ": " ++ show res) res
refocus' (Just n) pt@(PT path env tm)
      | Just (p', env', tm') <- findHole n env tm
             = PT (replaceTop p' path) env' tm'
      | Just (p', env', tm') <- findHole n [] (rebuildTerm tm path)
             = PT p' env' tm'
      | otherwise = pt
refocus' _ pt = pt

data Goal = GD { premises :: Env,
                 goalType :: Binder Term
               }

mkProofTerm :: Term -> ProofTerm
mkProofTerm tm = PT Top [] tm

getProofTerm :: ProofTerm -> Term
getProofTerm (PT path _ sub) = rebuildTerm sub path 

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

updateEnv [] e = e
updateEnv ns [] = []
updateEnv ns ((n, b) : env) = (n, fmap (updateSolvedTerm ns) b) : updateEnv ns env

updateSolvedPath [] t = t
updateSolvedPath ns Top = Top
updateSolvedPath ns (AppL p r) = AppL p (updateSolvedTerm ns r)
updateSolvedPath ns (AppR l p) = AppR (updateSolvedTerm ns l) p
updateSolvedPath ns (InBind n b sc) 
    = InBind n (updateSolvedPathB b) (updateSolvedTerm ns sc)
  where
    updateSolvedPathB (Binder b) = Binder (fmap (updateSolvedPath ns) b)
    updateSolvedPathB (LetT p v) = LetT (updateSolvedPath ns p) (updateSolvedTerm ns v)
    updateSolvedPathB (LetV v p) = LetV (updateSolvedTerm ns v) (updateSolvedPath ns p)
    updateSolvedPathB (GuessT p v) = GuessT (updateSolvedPath ns p) (updateSolvedTerm ns v)
    updateSolvedPathB (GuessV v p) = GuessV (updateSolvedTerm ns v) (updateSolvedPath ns p)
updateSolvedPath ns (InScope n (Hole ty) t)
    | Just v <- lookup n ns = case ns of
                                  [_] -> updateSolvedPath [(n,v)] t
                                  _ -> updateSolvedPath ns $
                                        updateSolvedPath [(n,v)] t
updateSolvedPath ns (InScope n b sc)
    = InScope n (fmap (updateSolvedTerm ns) b) (updateSolvedPath ns sc)

updateSolved :: [(Name, Term)] -> ProofTerm -> ProofTerm 
updateSolved xs pt@(PT path env sub) 
     = PT (updateSolvedPath xs path) 
          (updateEnv xs (filter (\(n, t) -> n `notElem` map fst xs) env)) 
          (updateSolvedTerm xs sub) 

goal :: Hole -> ProofTerm -> TC Goal
goal h pt@(PT path env sub) 
     | OK ginf <- g env sub = return ginf
     | otherwise = g [] (rebuildTerm sub path)
  where 
    g :: Env -> Term -> TC Goal
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
atHole h f c e pt -- @(PT path env sub) 
     = do let pt'@(PT path env sub) = refocus h pt
          (tm, u) <- atH f c env sub 
          return (PT path env tm, u)
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
bound_in (PT path _ tm) = bound_in_term (rebuildTerm tm path)

bound_in_term :: Term -> [Name]
bound_in_term (Bind n b sc) = n : bi b ++ bound_in_term sc
  where
    bi (Let t v) = bound_in_term t ++ bound_in_term v
    bi (Guess t v) = bound_in_term t ++ bound_in_term v
    bi b = bound_in_term (binderTy b)
bound_in_term (App f a) = bound_in_term f ++ bound_in_term a
bound_in_term _ = []


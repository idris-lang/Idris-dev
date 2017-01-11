{-|
Module      : Idris.Core.ProofTerm
Description : Proof term. implementation and utilities.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PatternGuards #-}
module Idris.Core.ProofTerm(
    ProofTerm, Goal(..), mkProofTerm, getProofTerm
  , resetProofTerm
  , updateSolved, updateSolvedTerm, updateSolvedTerm'
  , bound_in, bound_in_term, refocus, updsubst
  , Hole, RunTactic'
  , goal, atHole
  ) where

import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Core.Typecheck

import Control.Monad.State.Strict
import Data.List
import Debug.Trace

-- | A zipper over terms, in order to efficiently update proof terms.
data TermPath = Top
              | AppL (AppStatus Name) TermPath Term
              | AppR (AppStatus Name) Term TermPath
              | InBind Name BinderPath Term
              | InScope Name (Binder Term) TermPath
  deriving Show

-- | A zipper over binders, because terms and binders are mutually defined.
data BinderPath = Binder (Binder TermPath)
                | LetT TermPath Term
                | LetV Term TermPath
                | GuessT TermPath Term
                | GuessV Term TermPath
  deriving Show

-- | Replace the top of a term path with another term path. In other
-- words, "graft" one term path into another.
replaceTop :: TermPath -> TermPath -> TermPath
replaceTop p Top = p
replaceTop p (AppL s l t) = AppL s (replaceTop p l) t
replaceTop p (AppR s t r) = AppR s t (replaceTop p r)
replaceTop p (InBind n bp sc) = InBind n (replaceTopB p bp) sc
  where
    replaceTopB p (Binder b) = Binder (fmap (replaceTop p) b)
    replaceTopB p (LetT t v) = LetT (replaceTop p t) v
    replaceTopB p (LetV t v) = LetV t (replaceTop p v)
    replaceTopB p (GuessT t v) = GuessT (replaceTop p t) v
    replaceTopB p (GuessV t v) = GuessV t (replaceTop p v)
replaceTop p (InScope n b sc) = InScope n b (replaceTop p sc)

-- | Build a term from a zipper, given something to put in the hole.
rebuildTerm :: Term -> TermPath -> Term
rebuildTerm tm Top = tm
rebuildTerm tm (AppL s p a) = App s (rebuildTerm tm p) a
rebuildTerm tm (AppR s f p) = App s f (rebuildTerm tm p)
rebuildTerm tm (InScope n b p) = Bind n b (rebuildTerm tm p)
rebuildTerm tm (InBind n bp sc) = Bind n (rebuildBinder tm bp) sc

-- | Build a binder from a zipper, given something to put in the hole.
rebuildBinder :: Term -> BinderPath -> Binder Term
rebuildBinder tm (Binder p) = fmap (rebuildTerm tm) p
rebuildBinder tm (LetT p t) = Let (rebuildTerm tm p) t
rebuildBinder tm (LetV v p) = Let v (rebuildTerm tm p)
rebuildBinder tm (GuessT p t) = Guess (rebuildTerm tm p) t
rebuildBinder tm (GuessV v p) = Guess v (rebuildTerm tm p)

-- | Find the binding of a hole in a term. If present, return the path
-- to the hole's binding, the environment extended by the binders that
-- are crossed, and the actual binding term.
findHole :: Name -> Env -> Term -> Maybe (TermPath, Env, Term)
findHole n env t = fh' env Top t where
  fh' env path tm@(Bind x h sc)
      | hole h && n == x = Just (path, env, tm)
  fh' env path (App Complete _ _) = Nothing
  fh' env path (App s f a)
      | Just (p, env', tm) <- fh' env path a = Just (AppR s f p, env', tm)
      | Just (p, env', tm) <- fh' env path f = Just (AppL s p a, env', tm)
  fh' env path (Bind x b sc)
      | Just (bp, env', tm) <- fhB env path b = Just (InBind x bp sc, env', tm)
      | Just (p, env', tm) <- fh' ((x,RigW,b):env) path sc = Just (InScope x b p, env', tm)
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
                      subterm :: Term,
                      updates :: [(Name, Term)] }
  deriving Show

type RunTactic' a = Context -> Env -> Term -> StateT a TC Term
type Hole = Maybe Name -- Nothing = default hole, first in list in proof state

-- | Refocus the proof term zipper on a particular hole, if it
-- exists. If not, return the original proof term.
refocus :: Hole -> ProofTerm -> ProofTerm
refocus h t = let res = refocus' h t in res
--                   trace ("OLD: " ++ show t ++ "\n" ++
--                          "REFOCUSSED " ++ show h ++ ": " ++ show res) res
refocus' (Just n) pt@(PT path env tm ups)
      -- First look for the hole in the proof term as-is
      | Just (p', env', tm') <- findHole n env tm
             = PT (replaceTop p' path) env' tm' ups
      -- If it's not there, rebuild and look from the top
      | Just (p', env', tm') <- findHole n [] (rebuildTerm tm (updateSolvedPath ups path))
             = PT p' env' tm' []
      | otherwise = pt
refocus' _ pt = pt

data Goal = GD { premises :: Env,
                 goalType :: Binder Term
               }

mkProofTerm :: Term -> ProofTerm
mkProofTerm tm = PT Top [] tm []

getProofTerm :: ProofTerm -> Term
getProofTerm (PT path _ sub ups) = rebuildTerm sub (updateSolvedPath ups path)

resetProofTerm :: ProofTerm -> ProofTerm
resetProofTerm = mkProofTerm . getProofTerm

same :: Eq a => Maybe a -> a -> Bool
same Nothing n  = True
same (Just x) n = x == n

-- | Is a particular binder a hole or a guess?
hole :: Binder b -> Bool
hole (Hole _)    = True
hole (Guess _ _) = True
hole _           = False

-- | Given a list of solved holes, fill out the solutions in a term
updateSolvedTerm :: [(Name, Term)] -> Term -> Term
updateSolvedTerm xs x = fst $ updateSolvedTerm' xs x

-- | Given a list of solved holes, fill out the solutions in a
-- term. Return whether updates were performed, to facilitate sharing
-- when there are no updates.
updateSolvedTerm' :: [(Name, Term)] -> Term -> (Term, Bool)
updateSolvedTerm' [] x = (x, False)
updateSolvedTerm' xs x = updateSolved' xs x where
    -- This version below saves allocations, because it doesn't need to reallocate
    -- the term if there are no updates to do.
    -- The Bool is ugly, and probably 'Maybe' would be less ugly, but >>= is
    -- the wrong combinator. Feel free to tidy up as long as it's still as cheap :).
    updateSolved' [] x = (x, False)
    updateSolved' xs (Bind n (Hole ty) t)
        | Just v <- lookup n xs
            = case xs of
                   [_] -> (updsubst n v t, True) -- some may be Vs! Can't assume
                                              -- explicit names
                   _ -> let (t', _) = updateSolved' xs t in
                            (updsubst n v t', True)
    updateSolved' xs tm@(Bind n b t)
        = let (t', ut) = updateSolved' xs t
              (b', ub) = updateSolvedB' xs b in
              if ut || ub then (Bind n b' t', True)
                          else (tm, False)
    updateSolved' xs t@(App Complete f a) = (t, False)
    updateSolved' xs t@(App s f a)
        = let (f', uf) = updateSolved' xs f
              (a', ua) = updateSolved' xs a in
              if uf || ua then (App s f' a', True)
                          else (t, False)
    updateSolved' xs t@(P _ n@(MN _ _) _)
        | Just v <- lookup n xs = (v, True)
    updateSolved' xs t@(P nt n ty)
        = let (ty', ut) = updateSolved' xs ty in
              if ut then (P nt n ty', True) else (t, False)
    updateSolved' xs t = (t, False)

    updateSolvedB' xs b@(Let t v) = let (t', ut) = updateSolved' xs t
                                        (v', uv) = updateSolved' xs v in
                                        if ut || uv then (Let t' v', True)
                                                    else (b, False)
    updateSolvedB' xs b@(Guess t v) = let (t', ut) = updateSolved' xs t
                                          (v', uv) = updateSolved' xs v in
                                          if ut || uv then (Guess t' v', True)
                                                      else (b, False)
    updateSolvedB' xs b = let (ty', u) = updateSolved' xs (binderTy b) in
                              if u then (b { binderTy = ty' }, u) else (b, False)

    noneOf ns (P _ n _) | n `elem` ns = False
    noneOf ns (App s f a) = noneOf ns a && noneOf ns f
    noneOf ns (Bind n (Hole ty) t) = n `notElem` ns && noneOf ns ty && noneOf ns t
    noneOf ns (Bind n b t) = noneOf ns t && noneOfB ns b
      where
        noneOfB ns (Let t v) = noneOf ns t && noneOf ns v
        noneOfB ns (Guess t v) = noneOf ns t && noneOf ns v
        noneOfB ns b = noneOf ns (binderTy b)
    noneOf ns _ = True

-- | As 'subst', in TT, but takes advantage of knowing not to substitute
-- under Complete applications.
updsubst :: Eq n => n {-^ The id to replace -} ->
            TT n {-^ The replacement term -} ->
            TT n {-^ The term to replace in -} ->
            TT n
-- subst n v tm = instantiate v (pToV n tm)
updsubst n v tm = fst $ subst' 0 tm
  where
    -- keep track of updates to save allocations - this is a big win on
    -- large terms in particular
    -- ('Maybe' would be neater here, but >>= is not the right combinator.
    -- Feel free to tidy up, as long as it still saves allocating when no
    -- substitution happens...)
    subst' i (V x) | i == x = (v, True)
    subst' i (P _ x _) | n == x = (v, True)
    subst' i t@(P nt x ty)
         = let (ty', ut) = subst' i ty in
               if ut then (P nt x ty', True) else (t, False)
    subst' i t@(Bind x b sc) | x /= n
         = let (b', ub) = substB' i b
               (sc', usc) = subst' (i+1) sc in
               if ub || usc then (Bind x b' sc', True) else (t, False)
    subst' i t@(App Complete f a) = (t, False)
    subst' i t@(App s f a) = let (f', uf) = subst' i f
                                 (a', ua) = subst' i a in
                                 if uf || ua then (App s f' a', True) else (t, False)
    subst' i t@(Proj x idx) = let (x', u) = subst' i x in
                                  if u then (Proj x' idx, u) else (t, False)
    subst' i t = (t, False)

    substB' i b@(Let t v) = let (t', ut) = subst' i t
                                (v', uv) = subst' i v in
                                if ut || uv then (Let t' v', True)
                                            else (b, False)
    substB' i b@(Guess t v) = let (t', ut) = subst' i t
                                  (v', uv) = subst' i v in
                                  if ut || uv then (Guess t' v', True)
                                              else (b, False)
    substB' i b = let (ty', u) = subst' i (binderTy b) in
                      if u then (b { binderTy = ty' }, u) else (b, False)


-- | Apply solutions to an environment.
updateEnv :: [(Name, Term)] -> Env -> Env
updateEnv [] e = e
updateEnv ns [] = []
updateEnv ns ((n, r, b) : env) = (n, r, fmap (updateSolvedTerm ns) b) : updateEnv ns env

-- | Fill out solved holes in a term zipper.
updateSolvedPath :: [(Name, Term)] -> TermPath -> TermPath
updateSolvedPath [] t = t
updateSolvedPath ns Top = Top
updateSolvedPath ns t@(AppL Complete _ _) = t
updateSolvedPath ns t@(AppR Complete _ _) = t
updateSolvedPath ns (AppL s p r) = AppL s (updateSolvedPath ns p) (updateSolvedTerm ns r)
updateSolvedPath ns (AppR s l p) = AppR s (updateSolvedTerm ns l) (updateSolvedPath ns p)
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
updateSolved xs pt@(PT path env sub ups)
     = PT path -- (updateSolvedPath xs path)
          (updateEnv xs (filter (\(n, r, t) -> n `notElem` map fst xs) env))
          (updateSolvedTerm xs sub)
          (ups ++ xs)

goal :: Hole -> ProofTerm -> TC Goal
goal h pt@(PT path env sub ups)
--      | OK ginf <- g env sub = return ginf
     | otherwise = g [] (rebuildTerm sub (updateSolvedPath ups path))
  where
    g :: Env -> Term -> TC Goal
    g env (Bind n b@(Guess _ _) sc)
                        | same h n = return $ GD env b
                        | otherwise
                           = gb env b `mplus` g ((n, RigW, b):env) sc
    g env (Bind n b sc) | hole b && same h n = return $ GD env b
                        | otherwise
                           = g ((n, RigW, b):env) sc `mplus` gb env b
    g env (App Complete f a) = fail "Can't find hole"
    g env (App _ f a) = g env a `mplus` g env f
    g env t           = fail "Can't find hole"

    gb env (Let t v) = g env v `mplus` g env t
    gb env (Guess t v) = g env v `mplus` g env t
    gb env t = g env (binderTy t)

atHole :: Hole -> RunTactic' a -> Context -> Env -> ProofTerm ->
          StateT a TC (ProofTerm, Bool)
atHole h f c e pt -- @(PT path env sub)
     = do let PT path env sub ups = refocus h pt
          (tm, u) <- atH f c env sub
          return (PT path env tm ups, u)
--           if u then return (PT path env tm ups, u)
--                else do let PT path env sub ups = refocus h pt
--                        (tm, u) <- atH f c env sub
--                        return (PT path env tm ups, u)
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
                      else do (sc', u) <- atH f c ((n, RigW, b) : env) sc
                              return (Bind n b' sc', u)
    atH f c env binder@(Bind n b sc)
        | hole b && same h n = updated (f c env binder)
        | otherwise -- scope first
            = do (sc', u) <- atH f c ((n, RigW, b) : env) sc
                 if u then return (Bind n b sc', True)
                      else do (b', u) <- atHb f c env b
                              return (Bind n b' sc', u)
    atH tac c env (App s f a)  = ulift2 tac c env (App s) f a
    atH tac c env t            = return (t, False)

    atHb f c env (Let t v)   = ulift2 f c env Let t v
    atHb f c env (Guess t v) = ulift2 f c env Guess t v
    atHb f c env t           = do (ty', u) <- atH f c env (binderTy t)
                                  return (t { binderTy = ty' }, u)

bound_in :: ProofTerm -> [Name]
bound_in (PT path _ tm ups) = bound_in_term (rebuildTerm tm (updateSolvedPath ups path))

bound_in_term :: Term -> [Name]
bound_in_term (Bind n b sc) = n : bi b ++ bound_in_term sc
  where
    bi (Let t v) = bound_in_term t ++ bound_in_term v
    bi (Guess t v) = bound_in_term t ++ bound_in_term v
    bi b = bound_in_term (binderTy b)
bound_in_term (App _ f a) = bound_in_term f ++ bound_in_term a
bound_in_term _ = []

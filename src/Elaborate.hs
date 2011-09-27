{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

{- A high level language of tactic composition, for building
   elaborators from a high level language into the core theory.

   This is our interface to proof construction, rather than
   ProofState, because this gives us a language to build derived
   tactics out of the primitives.
-}

module Elaborate(module Elaborate, module ProofState) where

import ProofState
import Core
import Evaluate

import Control.Monad.State

-- I don't really want this here, but it's useful for the test shell
data Command = Theorem Name Raw
             | Eval Raw
             | Quit
             | Print Name
             | Tac (Elab ())

type Elab a = StateT (ProofState, String) TC a

runElab :: Elab a -> ProofState -> TC (ProofState, String)
runElab e ps = execStateT e (ps, "")

initElaborator :: Name -> Context -> Type -> ProofState
initElaborator = newProof

processTactic' t = do (p, logs) <- get
                      (p', log) <- lift $ processTactic t p
                      put (p', logs ++ log)
                      return ()

-- The primitives, from ProofState

attack :: Elab ()
attack = processTactic' Attack

claim :: Name -> Raw -> Elab ()
claim n t = processTactic' (Claim n t)

fill :: Raw -> Elab ()
fill t = processTactic' (Fill t)

unify_fill :: Raw -> Elab ()
unify_fill t = processTactic' (UnifyFill t)

solve :: Elab ()
solve = processTactic' Solve

regret :: Elab ()
regret = processTactic' Regret

compute :: Elab ()
compute = processTactic' Compute

eval_in :: Raw -> Elab ()
eval_in t = processTactic' (EvalIn t)

check_in :: Raw -> Elab ()
check_in t = processTactic' (CheckIn t)

intro :: Name -> Elab ()
intro n = processTactic' (Intro n)

forall :: Name -> Raw -> Elab ()
forall n t = processTactic' (Forall n t)

focus :: Name -> Elab ()
focus n = processTactic' (Focus n)

proofstate :: Elab ()
proofstate = processTactic' ProofState

qed :: Elab ()
qed = processTactic' QED

-- Some combinators on elaborations

-- Sequencing
-- infixr 5 ==>

-- (==>) :: Elab -> Elab -> Elab
-- (==>) t1 t2 ps = do (ps',  log')  <- t1 ps
--                     (ps'', log'') <- t2 ps'
--                     return (ps'', log' ++ log')
--              
-- -- Try a tactic, if it fails, try another
-- try :: Elab -> Elab -> Elab
-- try t1 t2 ps = case t1 ps of
--                     OK v -> return v
--                     _ -> t2 ps
-- 

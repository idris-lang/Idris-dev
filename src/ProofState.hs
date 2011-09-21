{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module ProofState where

import Typecheck
import Evaluate
import Core
import Control.Monad.State

data ProofState = PS { holes :: [Name], -- holes still to be solved
                       nextname :: Int, -- name supply
                       pterm :: Term    -- current proof term
                     }
                   
data Goal = GD { premises :: Env,
                 goalType :: Term
               }

data TacticAction = AddGoal Name
                  
type Tactic = Context -> Env -> Term -> StateT [TacticAction] TC Term
type Hole = Maybe Name -- Nothing = default hole, first in list in proof state

goal :: Hole -> Term -> Context -> TC Goal
goal h tm ctxt = g [] tm where
    g env (Bind n b sc) | hole b && same h n = return $ GD env (binderTy b)
                        | otherwise          = gb env b `mplus` g ((n,b):env) sc
    g env (App f t a) = g env f `mplus` g env t `mplus` g env a
    g env t           = Error "Can't find hole"

    gb env (Let t v) = g env t `mplus` g env v
    gb env (Guess t v) = g env t `mplus` g env v
    gb env t = g env (binderTy t)

tactic :: Hole -> Term -> Context -> Tactic -> StateT [TacticAction] TC Term
tactic h tm ctxt f = atH [] tm where
    atH env binder@(Bind n b sc) 
        | hole b && same h n = f ctxt env binder
        | otherwise          = do b'  <- atHb env b 
                                  sc' <- atH ((n,b):env) sc
                                  return (Bind n b' sc')
    atH env (App f t a)  = do f' <- atH env t; t' <- atH env t; a' <- atH env a
                              return (App f' t' a')
    atH env t            = do return t
    
    atHb env (Let t v)   = do t' <- atH env t
                              v' <- atH env v
                              return $ Let t' v'
    atHb env (Guess t v) = do t' <- atH env t
                              v' <- atH env v
                              return $ Let t' v'
    atHb env t           = do ty' <- atH env (binderTy t)
                              return $ t { binderTy = ty' }
    
same Nothing n  = True
same (Just x) n = x == n
 
hole (Hole _)    = True
hole (Guess _ _) = True



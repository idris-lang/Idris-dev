{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module ProofState where

import Typecheck
import Evaluate
import Core
import Control.Monad.State

data ProofState = PS { thname   :: Name,
                       holes    :: [Name], -- holes still to be solved
                       nextname :: Int,    -- name supply
                       pterm    :: Term,   -- current proof term
                       context  :: Context,
                       complete :: Bool
                     }
                   
data Goal = GD { premises :: Env,
                 goalType :: Binder Term
               }

data Command = Theorem Name Raw
             | Eval Raw
             | Quit
             | Tac Tactic

data Tactic = Attack
            | Claim Name Raw
            | Try Raw
            | Regret
            | Solve
            | QED

instance Show ProofState where
    show (PS nm [] _ tm _ _) = show nm ++ ": no more goals"
    show (PS nm (h:hs) _ tm ctxt _) 
          = let OK g = goal (Just h) tm ctxt in
                showEnv (premises g) ++ "\n" ++
                "-------------------------------- (" ++ show nm ++ 
                ") -------\n" ++
                show h ++ " : " ++ showG (goalType g) ++ "\n"
         where showEnv [] = ""
               showEnv ((n, b):bs) = "  " ++ show n ++ " : " ++ show (binderTy b) ++ "\n" ++
                                     showEnv bs
               showG (Guess t v) = show t ++ " =?= " ++ show v
               showG b = show (binderTy b)

holeName i = MN i "hole" 

newProof :: Name -> Context -> Type -> ProofState
newProof n ctxt ty = let h = holeName 0 in
                         PS n [h] 1 (Bind h (Hole ty) (V 0)) ctxt False

data TacticAction = AddGoal Name
                  | Log String

type RunTactic = Context -> Env -> Term -> StateT [TacticAction] TC Term
type Hole = Maybe Name -- Nothing = default hole, first in list in proof state

goal :: Hole -> Term -> Context -> TC Goal
goal h tm ctxt = g [] tm where
    g env (Bind n b sc) | hole b && same h n = return $ GD env b 
                        | otherwise          = gb env b `mplus` g ((n,b):env) sc
    g env (App f t a) = g env f `mplus` g env t `mplus` g env a
    g env t           = Error "Can't find hole"

    gb env (Let t v) = g env t `mplus` g env v
    gb env (Guess t v) = g env t `mplus` g env v
    gb env t = g env (binderTy t)

tactic :: Hole -> Term -> Context -> RunTactic -> StateT [TacticAction] TC Term
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

attack :: RunTactic
attack = undefined

claim :: Name -> Raw -> RunTactic
claim = undefined

regret :: RunTactic
regret = undefined

fill :: Raw -> RunTactic -- Try
fill = undefined

solve :: RunTactic
solve = undefined

processTactic :: Tactic -> ProofState -> TC (ProofState, String)
processTactic QED ps = case holes ps of
                           [] -> return (ps { complete = True }, "QED")
                           _  -> Error "Still holes to fill"
processTactic t ps   = case holes ps of
                           [] -> Error "Nothing to fill in"
                           (h:_)  -> do (ps', actions) <- runStateT (process t h ps) []
                                        return (ps', logs actions)
    where logs [] = ""
          logs (Log x : xs) = x ++ "\n" ++ logs xs
          logs (_     : xs) = logs xs

process :: Tactic -> Name -> ProofState -> StateT [TacticAction] TC ProofState
process (Try x) h ps = undefined


                              



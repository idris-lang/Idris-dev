{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module ProofState where

import Typecheck
import Evaluate
import Core

import Control.Monad.State
import Control.Applicative
import Data.List

data ProofState = PS { thname   :: Name,
                       holes    :: [Name], -- holes still to be solved
                       nextname :: Int,    -- name supply
                       pterm    :: Term,   -- current proof term
                       ptype    :: Type,   -- original goal
                       context  :: Context,
                       done     :: Bool
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
            | Fill Raw
            | Regret
            | Solve
            | EvalIn Raw
            | CheckIn Raw
            | Intro Name
            | ProofState
            | QED
-- Next: add 'EvalHere' and 'CheckHere' tactics

data TacticAction = AddGoal Name
                  | Solved Name
                  | Log String

-- Some utilites on proof and tactic states

instance Show ProofState where
    show (PS nm [] _ tm _ _ _) = show nm ++ ": no more goals"
    show (PS nm (h:hs) _ tm _ ctxt _) 
          = let OK g = goal (Just h) tm ctxt 
                wkenv = weakenEnv (premises g) in
                showPs wkenv (reverse wkenv) ++ "\n" ++
                "-------------------------------- (" ++ show nm ++ 
                ") -------\n" ++
                show h ++ " : " ++ showG wkenv (goalType g) ++ "\n"
         where showPs env [] = ""
               showPs env ((n, b):bs) 
                   = "  " ++ show n ++ " : " ++ showEnv env (binderTy b) ++ 
                     "\n" ++ showPs env bs
               showG ps (Guess t v) = showEnv ps t ++ " =?= " ++ showEnv ps v
               showG ps b = showEnv ps (binderTy b)

same Nothing n  = True
same (Just x) n = x == n
 
hole (Hole _)    = True
hole (Guess _ _) = True
hole _           = False

holeName i = MN i "hole" 

getName :: Monad m => String -> StateT TState m Name
getName tag = do (n, ts) <- get
                 put (n+1, ts)
                 return $ MN n tag

action :: Monad m => TacticAction -> StateT TState m ()
action a = do (n, ts) <- get
              put (n, a:ts)

newProof :: Name -> Context -> Type -> ProofState
newProof n ctxt ty = let h = holeName 0 in
                         PS n [h] 1 (Bind h (Hole ty) (V 0)) ty ctxt False

type TState = (Int, [TacticAction])
type RunTactic = Context -> Env -> Term -> StateT TState TC Term
type Hole = Maybe Name -- Nothing = default hole, first in list in proof state

goal :: Hole -> Term -> Context -> TC Goal
goal h tm ctxt = g [] tm where
    g env (Bind n b sc) | hole b && same h n = return $ GD env b 
                        | otherwise          = gb env b `mplus` g ((n,b):env) sc
    g env (App f a)   = g env f `mplus` g env a
    g env t           = Error "Can't find hole"

    gb env (Let t v) = g env t `mplus` g env v
    gb env (Guess t v) = g env t `mplus` g env v
    gb env t = g env (binderTy t)

tactic :: Hole -> ProofState -> Context -> RunTactic -> StateT TState TC ProofState
tactic h ps ctxt f = do let tm = pterm ps
                        tm' <- atH [] tm
                        return (ps { pterm = tm' })
  where
    atH env binder@(Bind n b sc) 
        | hole b && same h n = f ctxt (weakenEnv env) binder
        | otherwise          = pure Bind <*> pure n <*> atHb env b <*> atH ((n,b):env) sc
    atH env (App f a)    = pure App <*> atH env f <*> atH env a
    atH env t            = return t
    
    atHb env (Let t v)   = pure Let <*> atH env t <*> atH env v    
    atHb env (Guess t v) = pure Guess <*> atH env t <*> atH env v
    atHb env t           = do ty' <- atH env (binderTy t)
                              return $ t { binderTy = ty' }

attack :: RunTactic
attack ctxt env (Bind x (Hole t) sc) 
    = do h <- getName "hole"
         action (AddGoal h)
         return $ Bind x (Guess t (newtm h)) sc
  where
    newtm h = Bind h (Hole t) (V 0) 
attack ctxt env _ = fail "Not an attackable hole"

claim :: Name -> Raw -> RunTactic
claim = undefined

regret :: RunTactic
regret = undefined

fill :: Raw -> RunTactic -- Try
fill guess ctxt env (Bind x (Hole ty) sc) = 
    do (val, valty) <- lift $ check ctxt env guess 
       lift $ converts ctxt env valty ty
       return $ Bind x (Guess ty val) sc
fill _ _ _ _ = fail "Can't fill here."

solve :: RunTactic
solve ctxt env (Bind x (Guess ty val) sc)
   | pureTerm val = do action (Solved x)
                       return $ Bind x (Let ty val) sc
   | otherwise    = fail "I see a hole in your solution."
solve _ _ _ = fail "Not a guess."

intro :: Name -> RunTactic
intro n ctxt env (Bind x (Hole t) (V 0)) = 
    do let t' = normalise ctxt env t
       case t' of
           Bind y (Pi s) t -> return $ Bind n (Lam s) (Bind x (Hole t) (V 0))
           _ -> fail "Nothing to introduce"
intro ctxt env _ _ = fail "Can't introduce here."

check_in :: Raw -> RunTactic
check_in t ctxt env tm = 
    do (val, valty) <- lift $ check ctxt env t
       action (Log (showEnv env val ++ " : " ++ showEnv env valty))
       return tm

eval_in :: Raw -> RunTactic
eval_in t ctxt env tm = 
    do (val, valty) <- lift $ check ctxt env t
       action (Log (showEnv env (normalise ctxt env val) ++ " : " ++ showEnv env valty))
       return tm


processTactic :: Tactic -> ProofState -> TC (ProofState, String)
processTactic QED ps = case holes ps of
                           [] -> return (ps { done = True }, "Proof complete.")
                           _  -> Error "Still holes to fill."
processTactic ProofState ps = return (ps, show (pterm ps))
processTactic t ps   = case holes ps of
                           [] -> Error "Nothing to fill in."
                           (h:_)  -> do let n = nextname ps
                                        (ps',(n', actions)) <- runStateT (process t h ps) (n, [])
                                        return (ps' { nextname = n',
                                                      holes = goals (holes ps') actions }, 
                                                logs actions)
    where logs [] = ""
          logs (Log x : xs) = x ++ "\n" ++ logs xs
          logs (_     : xs) = logs xs

          goals g [] = g
          goals g (AddGoal n : xs) = goals (n : g) xs
          goals g (Solved n  : xs) = goals (g \\ [n]) xs
          goals g (_         : xs) = goals g xs


process :: Tactic -> Name -> ProofState -> StateT TState TC ProofState
process t h ps = tactic (Just h) ps (context ps) (mktac t)
   where mktac Attack      = attack
         mktac (Claim n r) = claim n r
         mktac (Fill r)    = fill r
         mktac Regret      = regret
         mktac Solve       = solve
         mktac (Intro n)   = intro n
         mktac (CheckIn r) = check_in r
         mktac (EvalIn r)  = eval_in r

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

{- Implements a proof state, some primitive tactics for manipulating
   proofs, and some high level commands for introducing new theorems,
   evaluation/checking inside the proof system, etc. --}

module ProofState(ProofState(..), newProof, envAtFocus, goalAtFocus,
                  Tactic(..), processTactic) where

import Typecheck
import Evaluate
import Core
import Unify

import Control.Monad.State
import Control.Applicative
import Data.List
import Debug.Trace

data ProofState = PS { thname   :: Name,
                       holes    :: [Name], -- holes still to be solved
                       nextname :: Int,    -- name supply
                       pterm    :: Term,   -- current proof term
                       ptype    :: Type,   -- original goal
                       previous :: Maybe ProofState, -- for undo
                       context  :: Context,
                       done     :: Bool
                     }
                   
data Goal = GD { premises :: Env,
                 goalType :: Binder Term
               }

data Tactic = Attack
            | Claim Name Raw
            | Fill Raw
            | UnifyFill Raw
            | Regret
            | Solve
            | Compute
            | EvalIn Raw
            | CheckIn Raw
            | Intro Name
            | Forall Name Raw
            | PatVar Name Raw
            | Focus Name
            | MoveLast Name
            | ProofState
            | Undo
            | QED

data TacticAction = AddGoal Name   -- add a new goal, solve immediately
                  | NextGoal Name  -- add a new goal, solve it after current one
                  | FocusGoal Name -- focus on this goal next
                  | MoveGoal Name  -- move this goal to the end of the hole queue
                  | Solved Name
                  | AlsoSolved Name Term -- goals solved by unification
                  | Log String

-- Some utilites on proof and tactic states

instance Show ProofState where
    show (PS nm [] _ tm _ _ _ _) = show nm ++ ": no more goals"
    show (PS nm (h:hs) _ tm _ i_ ctxt _) 
          = let OK g = goal (Just h) tm
                wkenv = premises g in
                showPs wkenv (reverse wkenv) ++ "\n" ++
                "-------------------------------- (" ++ show nm ++ 
                ") -------\n" ++
                show h ++ " : " ++ showG wkenv (goalType g) ++ "\n"
         where showPs env [] = ""
               showPs env ((n, Let t v):bs) 
                   = "  " ++ show n ++ " : " ++ 
                     showEnv env (normalise ctxt env t) ++ "   =   " ++
                     showEnv env (normalise ctxt env v) ++
                     "\n" ++ showPs env bs
               showPs env ((n, b):bs) 
                   = "  " ++ show n ++ " : " ++ 
                     showEnv env (normalise ctxt env (binderTy b)) ++ 
                     "\n" ++ showPs env bs
               showG ps (Guess t v) = showEnv ps (normalise ctxt ps t) ++ 
                                         " =?= " ++ showEnv ps v
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
newProof n ctxt ty = let h = holeName 0 
                         ty' = vToP ty in
                         PS n [h] 1 (Bind h (Hole ty') (P Bound h ty')) ty Nothing ctxt False

type TState = (Int, [TacticAction])
type RunTactic = Context -> Env -> Term -> StateT TState TC Term
type Hole = Maybe Name -- Nothing = default hole, first in list in proof state

envAtFocus :: ProofState -> TC Env
envAtFocus ps 
    | not $ null (holes ps) = do g <- goal (Just (head (holes ps))) (pterm ps)
                                 return (premises g)
    | otherwise = fail "No holes"

goalAtFocus :: ProofState -> TC Type
goalAtFocus ps
    | not $ null (holes ps) = do g <- goal (Just (head (holes ps))) (pterm ps)
                                 return (binderTy (goalType g))

goal :: Hole -> Term -> TC Goal
goal h tm = g [] tm where
    g env (Bind n b sc) | hole b && same h n = return $ GD env b 
                        | otherwise          
                           = gb env b `mplus` g ((n, b):env) sc
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
        | hole b && same h n = f ctxt env binder
        | otherwise          
            = pure Bind <*> pure n <*> atHb env b <*> atH ((n,b) : env) sc
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
    newtm h = Bind h (Hole t) (P Bound h t) 
attack ctxt env _ = fail "Not an attackable hole"

claim :: Name -> Raw -> RunTactic
claim n ty ctxt env t =
    do (tyv, tyt) <- lift $ check ctxt env ty
       lift $ isSet ctxt env tyt
       action (NextGoal n)
       return $ Bind n (Hole tyv) t -- (weakenTm 1 t)

focus :: Name -> RunTactic
focus n ctxt env t = do action (FocusGoal n)
                        return t 

movelast :: Name -> RunTactic
movelast n ctxt env t = do action (MoveGoal n)
                           return t 

-- Hmmm. YAGNI?
regret :: RunTactic
regret = undefined

fill :: Raw -> RunTactic
fill guess ctxt env (Bind x (Hole ty) sc) = 
    do (val, valty) <- lift $ check ctxt env guess 
       lift $ converts ctxt env valty ty
       return $ Bind x (Guess ty val) sc
fill _ _ _ _ = fail "Can't fill here."

-- As fill, but attempts to solve other goals by unification

unify_fill :: Raw -> RunTactic
unify_fill guess ctxt env (Bind x (Hole ty) sc) =
    do (val, valty) <- lift $ check ctxt env guess
       ns <- lift $ unify ctxt env valty ty
       solve_all ns
       return $ Bind x (Guess ty val) sc
  where
    solve_all [] = return ()
    solve_all ((n, tm): ns) = do action (AlsoSolved n tm)
                                 solve_all ns
unify_fill _ _ _ _ = fail "Can't fill here."

solve :: RunTactic
solve ctxt env (Bind x (Guess ty val) sc)
   | pureTerm val = do action (Solved x)
                       return $ Bind x (Let ty val) sc -- instantiate val (pToV x sc)
   | otherwise    = fail "I see a hole in your solution."
solve _ _ _ = fail "Not a guess."

intro :: Name -> RunTactic
intro n ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do let t' = normalise ctxt env t
       case t' of
           Bind y (Pi s) t -> let t' = instantiate (P Bound n s) (pToV y t) in 
                                  return $ Bind n (Lam s) (Bind x (Hole t') (P Bound x t'))
           _ -> fail "Nothing to introduce"
intro ctxt env _ _ = fail "Can't introduce here."

forall :: Name -> Raw -> RunTactic
forall n ty ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do (tyv, tyt) <- lift $ check ctxt env ty
       lift $ isSet ctxt env tyt
       lift $ isSet ctxt env t
       return $ Bind n (Pi tyv) (Bind x (Hole t) (P Bound x t))

patvar :: Name -> Raw -> RunTactic
patvar n ty ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do (tyv, tyt) <- lift $ check ctxt env ty
       lift $ isSet ctxt env tyt
       return $ Bind n (PVar tyv) (Bind x (Hole t) (P Bound x t))

compute :: RunTactic
compute ctxt env (Bind x (Hole ty) sc) =
    do return $ Bind x (Hole (normalise ctxt env ty)) sc
        
check_in :: Raw -> RunTactic
check_in t ctxt env tm = 
    do (val, valty) <- lift $ check ctxt env t
       action (Log (showEnv env val ++ " : " ++ showEnv env valty))
       return tm

eval_in :: Raw -> RunTactic
eval_in t ctxt env tm = 
    do (val, valty) <- lift $ check ctxt env t
       let val' = normalise ctxt env val
       let valty' = normalise ctxt env valty
       action (Log (showEnv env val ++ " : " ++ 
                    showEnv env valty ++ 
--                     " in " ++ show env ++ 
                    " ==>\n " ++
                    showEnv env val' ++ " : " ++ 
                    showEnv env valty'))
       return tm


processTactic :: Tactic -> ProofState -> TC (ProofState, String)
processTactic QED ps = case holes ps of
                           [] -> let tm = finalise (pterm ps) in
                                     return (ps { done = True, pterm = tm }, 
                                             "Proof complete: " ++ showEnv [] tm)
                           _  -> Error "Still holes to fill."
processTactic ProofState ps = return (ps, showEnv [] (pterm ps))
processTactic Undo ps = case previous ps of
                            Nothing -> Error "Nothing to undo."
                            Just pold -> return (pold, "")
processTactic t ps   
    = case holes ps of
        [] -> Error "Nothing to fill in."
        (h:_)  -> do let n = nextname ps
                     (ps', (n', actions)) <- runStateT (process t h ps) (n, [])
                     return (ps' { nextname = n',
                                   pterm = updateSolved (getSolved actions) (pterm ps'),
                                   holes = goals (holes ps') actions, 
                                   previous = Just ps }, 
                                   logs actions)
    where logs [] = ""
          logs (Log x : xs) = x ++ "\n" ++ logs xs
          logs (_     : xs) = logs xs

          goals g [] = g
          goals g      (AddGoal n  : xs) = goals (n : g) xs
          goals (g:gs) (NextGoal n : xs) = goals (g : n : gs) xs
          goals g     (FocusGoal n : xs) 
                            | n `elem` g = goals (n : (g \\ [n])) xs
          goals g      (MoveGoal n : xs) 
                            | n `elem` g = goals ((g \\ [n]) ++ [n]) xs
          goals g      (Solved n   : xs) = goals (g \\ [n]) xs
          goals g (AlsoSolved n tm : xs) = goals (g \\ [n]) xs
          goals g      (_          : xs) = goals g xs

          getSolved [] = []
          getSolved (AlsoSolved n tm : xs) = (n, tm) : getSolved xs
          getSolved (_               : xs) = getSolved xs

          updateSolved xs (Bind n b@(Hole _) t)
              | Just v <- lookup n xs = Bind n (Let (binderTy b) v) (updateSolved xs t)
          updateSolved xs (Bind n b t) 
              | otherwise = Bind n (fmap (updateSolved xs) b) (updateSolved xs t)
          updateSolved xs (App f a) = App (updateSolved xs f) (updateSolved xs a)
          updateSolved xs t = t

process :: Tactic -> Name -> ProofState -> StateT TState TC ProofState
process t h ps = tactic (Just h) ps (context ps) (mktac t)
   where mktac Attack        = attack
         mktac (Claim n r)   = claim n r
         mktac (Fill r)      = fill r
         mktac (UnifyFill r) = unify_fill r
         mktac Regret        = regret
         mktac Solve         = solve
         mktac Compute       = compute
         mktac (Intro n)     = intro n
         mktac (Forall n t)  = forall n t
         mktac (PatVar n t)  = patvar n t
         mktac (CheckIn r)   = check_in r
         mktac (EvalIn r)    = eval_in r
         mktac (Focus n)     = focus n
         mktac (MoveLast n)  = movelast n

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

{- A high level language of tactic composition, for building
   elaborators from a high level language into the core theory.

   This is our interface to proof construction, rather than
   ProofState, because this gives us a language to build derived
   tactics out of the primitives.
-}

module Core.Elaborate(module Core.Elaborate, 
                      module Core.ProofState) where

import Core.ProofState
import Core.TT
import Core.Evaluate
import Core.Typecheck

import Control.Monad.State
import Data.Char
import Debug.Trace

-- I don't really want this here, but it's useful for the test shell
data Command = Theorem Name Raw
             | Eval Raw
             | Quit
             | Print Name
             | Tac (Elab ())

type Elab a = StateT (ProofState, String) TC a

runElab :: Elab a -> ProofState -> TC (a, (ProofState, String))
runElab e ps = runStateT e (ps, "")

execElab :: Elab a -> ProofState -> TC (ProofState, String)
execElab e ps = execStateT e (ps, "")

initElaborator :: Name -> Context -> Type -> ProofState
initElaborator = newProof

elaborate :: Context -> Name -> Type -> Elab a -> TC (a, String)
elaborate ctxt n ty elab = do let ps = initElaborator n ctxt ty
                              (a, (ps', str)) <- runElab elab ps
                              return (a, str)

processTactic' t = do (p, logs) <- get
                      (p', log) <- lift $ processTactic t p
                      put (p', logs ++ log)
                      return ()

-- Some handy gadgets for pulling out bits of state

-- get the global context
get_context :: Elab Context
get_context = do (p, _) <- get
                 return (context p)

-- get the proof term
get_term :: Elab Term
get_term = do (p, _) <- get
              return (pterm p)

-- get the local context at the currently in focus hole
get_env :: Elab Env
get_env = do (p, _) <- get
             lift $ envAtFocus p

get_holes :: Elab [Name]
get_holes = do (p, _) <- get
               return (holes p)

-- get the current goal type
goal :: Elab Type
goal = do (p, _) <- get
          lift $ goalAtFocus p

-- typecheck locally
get_type :: Raw -> Elab Type
get_type tm = do ctxt <- get_context
                 env <- get_env
                 (val, ty) <- lift $ check ctxt env tm
                 return (finalise ty)

-- given a desired hole name, return a unique hole name
unique_hole :: Name -> Elab Name
unique_hole n = do (p, _) <- get
                   env <- get_env
                   return (uniq n (holes p ++ map fst env))
  where
    uniq n hs | n `elem` hs = uniq (next n) hs
              | otherwise   = n

next (MN i n)    = MN (i+1) n
next (UN (x:xs)) = let (num', nm') = span isDigit (reverse x)
                       nm = reverse nm'
                       num = readN (reverse num') in
                           UN ((nm ++ show (num+1)) : xs)
  where
    readN "" = 0
    readN x  = read x

elog :: String -> Elab ()
elog str = do (p, logs) <- get
              put (p, logs ++ str ++ "\n")

-- The primitives, from ProofState

attack :: Elab ()
attack = processTactic' Attack

claim :: Name -> Raw -> Elab ()
claim n t = processTactic' (Claim n t)

exact :: Raw -> Elab ()
exact t = processTactic' (Exact t)

fill :: Raw -> Elab ()
fill t = processTactic' (Fill t)

prep_fill :: Name -> [Name] -> Elab ()
prep_fill n ns = processTactic' (PrepFill n ns)

complete_fill :: Elab ()
complete_fill = processTactic' CompleteFill

solve :: Elab ()
solve = processTactic' Solve

start_unify :: Name -> Elab ()
start_unify n = processTactic' (StartUnify n)

end_unify :: Elab ()
end_unify = processTactic' EndUnify

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

patvar :: Name -> Elab ()
patvar n = processTactic' (PatVar n)

patbind :: Name -> Elab ()
patbind n = processTactic' (PatBind n)

focus :: Name -> Elab ()
focus n = processTactic' (Focus n)

movelast :: Name -> Elab ()
movelast n = processTactic' (MoveLast n)

proofstate :: Elab ()
proofstate = processTactic' ProofState

qed :: Elab Term
qed = do processTactic' QED
         (p, _) <- get
         return (pterm p)

undo :: Elab ()
undo = processTactic' Undo


prepare_apply :: Raw -> [Bool] -> Elab [Name]
prepare_apply fn imps =
    do ty <- get_type fn
       ctxt <- get_context
       env <- get_env
       -- let claims = getArgs ty imps
       claims <- doClaims (normalise ctxt env ty) imps []
       (p, s) <- get
       -- reverse the claims we made so that args go left to right
       let n = length (filter not imps)
       let (h : hs) = holes p
       put (p { holes = h : (reverse (take n hs) ++ drop n hs) }, s)
       return claims
  where
    doClaims (Bind n' (Pi t) sc) (i : is) claims =
        do n <- unique_hole n'
           when (null claims) (start_unify n)
           let sc' = instantiate (P Bound n t) sc
           claim n (forget t)
           when i (movelast n)
           doClaims sc' is (n : claims)
    doClaims t [] claims = return (reverse claims)
    doClaims _ _ _ = fail "Wrong number of arguments"

apply :: Raw -> [Bool] -> Elab [Name]
apply fn imps = 
    do args <- prepare_apply fn imps
       fill (raw_apply fn (map Var args))
       -- *Don't* solve the arguments we're specifying by hand.
       -- (remove from unified list before calling end_unify)
       let dontunify = map fst (filter (not.snd) (zip args imps))
       (p, s) <- get
       let (n, hs) = unified p
       let unify = (n, filter (\ (n, t) -> not (n `elem` dontunify)) hs)
       put (p { unified = unify }, s)
       end_unify
       return args

apply_elab :: Name -> [Maybe (Elab ())] -> Elab ()
apply_elab n args = 
    do ty <- get_type (Var n)
       ctxt <- get_context
       env <- get_env
       claims <- doClaims (normalise ctxt env ty) args []
       prep_fill n (map fst claims)
       elabClaims claims
       complete_fill
       end_unify
  where
    doClaims (Bind n' (Pi t) sc) (i : is) claims =
        do n <- unique_hole n'
           when (null claims) (start_unify n)
           let sc' = instantiate (P Bound n t) sc
           claim n (forget t)
           doClaims sc' is ((n, i) : claims)
    doClaims t [] claims = return (reverse claims)
    doClaims _ _ _ = fail "Wrong number of arguments"

    elabClaims [] = return ()
    elabClaims ((n, Nothing) : xs) = elabClaims xs
    elabClaims ((n, Just elaboration) : xs)  =
        do (p, _) <- get
           focus n; elaboration; elabClaims xs

simple_app :: Elab () -> Elab () -> Elab ()
simple_app fun arg =
    do a <- unique_hole (MN 0 "a")
       b <- unique_hole (MN 0 "b")
       f <- unique_hole (MN 0 "f")
       s <- unique_hole (MN 0 "s")
       claim a (RSet 0)
       claim b (RSet 0)
       claim f (RBind (MN 0 "aX") (Pi (Var a)) (Var b))
       start_unify s
       claim s (Var a)
       prep_fill f [s]
       focus f; fun
       focus s; arg
       complete_fill
       end_unify

-- Abstract over an argument of unknown type, giving a name for the hole
-- which we'll fill with the argument type too.
arg :: Name -> Name -> Elab ()
arg n tyhole = do ty <- unique_hole tyhole
                  claim ty (RSet 0)
                  forall n (Var ty)

-- Try a tactic, if it fails, try another
try :: Elab a -> Elab a -> Elab a
try t1 t2 = do s <- get
               case runStateT t1 s of
                    OK (v, s') -> do put s'
                                     return v
                    _ -> t2


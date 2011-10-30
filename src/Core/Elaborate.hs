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

data ElabState = ES ProofState String (Maybe ElabState)
  deriving Show
type Elab a = StateT ElabState TC a

proof :: ElabState -> ProofState
proof (ES p _ _) = p

saveState :: Elab ()
saveState = do e@(ES p s _) <- get
               put (ES p s (Just e))

loadState :: Elab ()
loadState = do (ES p s e) <- get
               case e of
                  Just st -> put st
                  _ -> fail "Nothing to undo"

erun :: FC -> Elab a -> Elab a
erun f elab = do s <- get
                 case runStateT elab s of
                    OK (a, s')     -> do put s'
                                         return a
                    Error (At f e) -> lift $ Error (At f e)
                    Error e        -> lift $ Error (At f e)

runElab :: Elab a -> ProofState -> TC (a, ElabState)
runElab e ps = runStateT e (ES ps "" Nothing)

execElab :: Elab a -> ProofState -> TC ElabState
execElab e ps = execStateT e (ES ps "" Nothing)

initElaborator :: Name -> Context -> Type -> ProofState
initElaborator = newProof

elaborate :: Context -> Name -> Type -> Elab a -> TC (a, String)
elaborate ctxt n ty elab = do let ps = initElaborator n ctxt ty
                              (a, ES ps' str _) <- runElab elab ps
                              return (a, str)

processTactic' t = do ES p logs prev <- get
                      (p', log) <- lift $ processTactic t p
                      put (ES p' (logs ++ log) prev)
                      return ()

-- Some handy gadgets for pulling out bits of state

-- get the global context
get_context :: Elab Context
get_context = do ES p _ _ <- get
                 return (context p)

-- get the proof term
get_term :: Elab Term
get_term = do ES p _ _ <- get
              return (pterm p)

-- get the local context at the currently in focus hole
get_env :: Elab Env
get_env = do ES p _ _ <- get
             lift $ envAtFocus p

get_holes :: Elab [Name]
get_holes = do ES p _ _ <- get
               return (holes p)

-- get the current goal type
goal :: Elab Type
goal = do ES p _ _ <- get
          b <- lift $ goalAtFocus p
          return (binderTy b)

-- typecheck locally
get_type :: Raw -> Elab Type
get_type tm = do ctxt <- get_context
                 env <- get_env
                 (val, ty) <- lift $ check ctxt env tm
                 return (finalise ty)

-- get holes we've deferred for later definition
get_deferred :: Elab [Name]
get_deferred = do ES p _ _ <- get
                  return (deferred p)

-- given a desired hole name, return a unique hole name
unique_hole :: Name -> Elab Name
unique_hole n = do ES p _ _ <- get
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
elog str = do ES p logs prev <- get
              put (ES p (logs ++ str ++ "\n") prev)

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

letbind :: Name -> Raw -> Raw -> Elab ()
letbind n t v = processTactic' (LetBind n t v)

patvar :: Name -> Elab ()
patvar n = processTactic' (PatVar n)

patbind :: Name -> Elab ()
patbind n = processTactic' (PatBind n)

focus :: Name -> Elab ()
focus n = processTactic' (Focus n)

movelast :: Name -> Elab ()
movelast n = processTactic' (MoveLast n)

defer :: Name -> Elab ()
defer n = processTactic' (Defer n)

proofstate :: Elab ()
proofstate = processTactic' ProofState

qed :: Elab Term
qed = do processTactic' QED
         ES p _ _ <- get
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
       ES p s prev <- get
       -- reverse the claims we made so that args go left to right
       let n = length (filter not imps)
       let (h : hs) = holes p
       put (ES (p { holes = h : (reverse (take n hs) ++ drop n hs) }) s prev)
       return claims
  where
    doClaims (Bind n' (Pi t) sc) (i : is) claims =
        do n <- unique_hole (mkMN n')
           when (null claims) (start_unify n)
           let sc' = instantiate (P Bound n t) sc
           claim n (forget t)
           when i (movelast n)
           doClaims sc' is (n : claims)
    doClaims t [] claims = return (reverse claims)
    doClaims _ _ _ = fail $ "Wrong number of arguments for " ++ show fn

    mkMN n@(MN _ _) = n
    mkMN n@(UN [x]) = MN 0 x

apply :: Raw -> [Bool] -> Elab [Name]
apply fn imps = 
    do args <- prepare_apply fn imps
       fill (raw_apply fn (map Var args))
       -- *Don't* solve the arguments we're specifying by hand.
       -- (remove from unified list before calling end_unify)
       let dontunify = map fst (filter (not.snd) (zip args imps))
       ES p s prev <- get
       let (n, hs) = unified p
       let unify = (n, filter (\ (n, t) -> not (n `elem` dontunify)) hs)
       put (ES (p { unified = unify }) s prev)
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
        do n <- unique_hole (mkMN n')
           when (null claims) (start_unify n)
           let sc' = instantiate (P Bound n t) sc
           claim n (forget t)
           doClaims sc' is ((n, i) : claims)
    doClaims t [] claims = return (reverse claims)
    doClaims _ _ _ = fail $ "Wrong number of arguments for " ++ show n

    elabClaims [] = return ()
    elabClaims ((n, Nothing) : xs) = elabClaims xs
    elabClaims ((n, Just elaboration) : xs)  =
        do ES p _ _ <- get
           focus n; elaboration; elabClaims xs

    mkMN n@(MN _ _) = n
    mkMN n@(UN [x]) = MN 0 x

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
       focus s; arg -- need to work out the type of the arg, so do it first
       focus f; fun
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
                    _ -> do put s; t2


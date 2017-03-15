{-|
Module      : Idris.Core.Elaborate
Description : A high level language of tactic composition, for building elaborators from a high level language into the core theory.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.

This is our interface to proof construction, rather than ProofState,
because this gives us a language to build derived tactics out of the
primitives.
-}

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PatternGuards #-}
module Idris.Core.Elaborate (
    module Idris.Core.Elaborate
  , module Idris.Core.ProofState
  ) where

import Idris.Core.DeepSeq
import Idris.Core.Evaluate
import Idris.Core.ProofState
import Idris.Core.ProofTerm (bound_in, bound_in_term, getProofTerm, mkProofTerm,
                             refocus)
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Core.Unify
import Idris.Core.WHNF

import Util.Pretty hiding (fill)

import Control.DeepSeq
import Control.Monad.State.Strict
import Data.Char
import Data.List
import Debug.Trace

data ElabState aux = ES (ProofState, aux) String (Maybe (ElabState aux))
  deriving Show

type Elab' aux a = StateT (ElabState aux) TC a
type Elab a = Elab' () a

proof :: ElabState aux -> ProofState
proof (ES (p, _) _ _) = p

-- Insert a 'proofSearchFail' error if necessary to shortcut any further
-- fruitless searching
proofFail :: Elab' aux a -> Elab' aux a
proofFail e = do s <- get
                 case runStateT e s of
                      OK (a, s') -> do put s'
                                       return $! a
                      Error err -> lift $ Error (ProofSearchFail err)

explicit :: Name -> Elab' aux ()
explicit n = do ES (p, a) s m <- get
                let p' = p { dontunify = n : dontunify p }
                put (ES (p', a) s m)

-- Add a name that's okay to use in proof search (typically either because
-- it was given explicitly on the lhs, or intrduced as an explicit lambda
-- or let binding)
addPSname :: Name -> Elab' aux ()
addPSname n@(UN _)
     = do ES (p, a) s m <- get
          let p' = p { psnames = n : psnames p }
          put (ES (p', a) s m)
addPSname _ = return () -- can only use user given names

getPSnames :: Elab' aux [Name]
getPSnames = do ES (p, a) s m <- get
                return (psnames p)

saveState :: Elab' aux ()
saveState = do e@(ES p s _) <- get
               put (ES p s (Just e))

loadState :: Elab' aux ()
loadState = do (ES p s e) <- get
               case e of
                  Just st -> put st
                  _ -> lift $ Error . Msg $ "Nothing to undo"

getNameFrom :: Name -> Elab' aux Name
getNameFrom n = do (ES (p, a) s e) <- get
                   let next = nextname p
                   let p' = p { nextname = next + 1 }
                   put (ES (p', a) s e)
                   let n' = case n of
                        UN x -> MN (next+100) x
                        MN i x -> if i == 99999
                                     then MN (next+500) x
                                     else MN (next+100) x
                        NS (UN x) s -> MN (next+100) x
                        _ -> n
                   return $! n'

setNextName :: Elab' aux ()
setNextName = do env <- get_env
                 ES (p, a) s e <- get
                 let pargs = map fst (getArgTys (ptype p))
                 initNextNameFrom (pargs ++ map fstEnv env)

initNextNameFrom :: [Name] -> Elab' aux ()
initNextNameFrom ns = do ES (p, a) s e <- get
                         let n' = maxName (nextname p) ns
                         put (ES (p { nextname = n' }, a) s e)
  where
    maxName m ((MN i _) : xs) = maxName (max m i) xs
    maxName m (_ : xs) = maxName m xs
    maxName m [] = m + 1


-- | Transform the error returned by an elaboration script, preserving
-- location information and proof search failure messages.
transformErr :: (Err -> Err) -> Elab' aux a -> Elab' aux a
transformErr f elab = do s <- get
                         case runStateT elab s of
                           OK (a, s') -> do put s'
                                            return $! a
                           Error e -> lift $ Error (rewriteErr e)

    where
      rewriteErr (At f e) = At f (rewriteErr e)
      rewriteErr (ProofSearchFail e) = ProofSearchFail (rewriteErr e)
      rewriteErr e = f e

errAt :: String -> Name -> Maybe Type -> Elab' aux a -> Elab' aux a
errAt thing n ty = transformErr (Elaborating thing n ty)


erunAux :: FC -> Elab' aux a -> Elab' aux (a, aux)
erunAux f elab
    = do s <- get
         case runStateT elab s of
            OK (a, s')     -> do put s'
                                 aux <- getAux
                                 return $! (a, aux)
            Error (ProofSearchFail (At f e))
                           -> lift $ Error (ProofSearchFail (At f e))
            Error (At f e) -> lift $ Error (At f e)
            Error e        -> lift $ Error (At f e)

erun :: FC -> Elab' aux a -> Elab' aux a
erun f e = do (x, _) <- erunAux f e
              return x

runElab :: aux -> Elab' aux a -> ProofState -> TC (a, ElabState aux)
runElab a e ps = runStateT e (ES (ps, a) "" Nothing)

execElab :: aux -> Elab' aux a -> ProofState -> TC (ElabState aux)
execElab a e ps = execStateT e (ES (ps, a) "" Nothing)

initElaborator :: Name -- ^ the name of what's to be elaborated
               -> String -- ^ the current source file
               -> Context -- ^ the current global context
               -> Ctxt TypeInfo -- ^ the value of the idris_datatypes field of IState
               -> Int -- ^ the value of the idris_name field of IState
               -> Type -- ^ the goal type
               -> ProofState
initElaborator = newProof

elaborate :: String -> Context -> Ctxt TypeInfo -> Int -> Name -> Type -> aux -> Elab' aux a -> TC (a, String)
elaborate tcns ctxt datatypes globalNames n ty d elab =
  do let ps = initElaborator n tcns ctxt datatypes globalNames ty
     (a, ES ps' str _) <- runElab d elab ps
     return $! (a, str)

-- | Modify the auxiliary state
updateAux :: (aux -> aux) -> Elab' aux ()
updateAux f = do ES (ps, a) l p <- get
                 put (ES (ps, f a) l p)

-- | Get the auxiliary state
getAux :: Elab' aux aux
getAux = do ES (ps, a) _ _ <- get
            return $! a

-- | Set whether to show the unifier log
unifyLog :: Bool -> Elab' aux ()
unifyLog log = do ES (ps, a) l p <- get
                  put (ES (ps { unifylog = log }, a) l p)

getUnifyLog :: Elab' aux Bool
getUnifyLog = do ES (ps, a) l p <- get
                 return (unifylog ps)

-- | Process a tactic within the current elaborator state
processTactic' :: Tactic -> Elab' aux ()
processTactic' t = do ES (p, a) logs prev <- get
                      (p', log) <- lift $ processTactic t p
                      put (ES (p', a) (logs ++ log) prev)
                      return $! ()

updatePS :: (ProofState -> ProofState) -> Elab' aux ()
updatePS f = do ES (ps, a) logs prev <- get
                put $ ES (f ps, a) logs prev

now_elaborating :: FC -> Name -> Name -> Elab' aux ()
now_elaborating fc f a = updatePS (nowElaboratingPS fc f a)
done_elaborating_app :: Name -> Elab' aux ()
done_elaborating_app f = updatePS (doneElaboratingAppPS f)
done_elaborating_arg :: Name -> Name -> Elab' aux ()
done_elaborating_arg f a = updatePS (doneElaboratingArgPS f a)
elaborating_app :: Elab' aux [(FC, Name, Name)]
elaborating_app = do ES (ps, _) _ _ <- get
                     return $ map (\ (FailContext x y z) -> (x, y, z))
                                  (while_elaborating ps)

-- Some handy gadgets for pulling out bits of state

-- | Get the global context
get_context :: Elab' aux Context
get_context = do ES p _ _ <- get
                 return $! (context (fst p))

-- | Update the context.
-- (should only be used for adding temporary definitions or all sorts of
--  stuff could go wrong)
set_context :: Context -> Elab' aux ()
set_context ctxt = do ES (p, a) logs prev <- get
                      put (ES (p { context = ctxt }, a) logs prev)

get_datatypes :: Elab' aux (Ctxt TypeInfo)
get_datatypes = do ES p _ _ <- get
                   return $! (datatypes (fst p))

set_datatypes :: Ctxt TypeInfo -> Elab' aux ()
set_datatypes ds = do ES (p, a) logs prev <- get
                      put (ES (p { datatypes = ds }, a) logs prev)

get_global_nextname :: Elab' aux Int
get_global_nextname = do ES (ps, _) _ _ <- get
                         return (global_nextname ps)

set_global_nextname :: Int -> Elab' aux ()
set_global_nextname i = do ES (ps, a) logs prev <- get
                           put $ ES (ps { global_nextname = i}, a) logs prev

-- | get the proof term
get_term :: Elab' aux Term
get_term = do ES p _ _ <- get
              return $! (getProofTerm (pterm (fst p)))

-- | modify the proof term
update_term :: (Term -> Term) -> Elab' aux ()
update_term f = do ES (p,a) logs prev <- get
                   let p' = p { pterm = mkProofTerm (f (getProofTerm (pterm p))) }
                   put (ES (p', a) logs prev)

-- | get the local context at the currently in focus hole
get_env :: Elab' aux Env
get_env = do ES p _ _ <- get
             lift $ envAtFocus (fst p)

get_inj :: Elab' aux [Name]
get_inj = do ES p _ _ <- get
             return $! (injective (fst p))

get_holes :: Elab' aux [Name]
get_holes = do ES p _ _ <- get
               return $! (holes (fst p))

get_usedns :: Elab' aux [Name]
get_usedns = do ES p _ _ <- get
                let bs = bound_in (pterm (fst p)) ++
                         bound_in_term (ptype (fst p))
                let nouse = holes (fst p) ++ bs ++ dontunify (fst p) ++ usedns (fst p)
                return $! nouse

get_probs :: Elab' aux Fails
get_probs = do ES p _ _ <- get
               return $! (problems (fst p))

-- | Return recently solved names (that is, the names solved since the
-- last call to get_recents)
get_recents :: Elab' aux [Name]
get_recents = do ES (p, a) l prev <- get
                 put (ES (p { recents = [] }, a) l prev)
                 return (recents p)

-- | get the current goal type
goal :: Elab' aux Type
goal = do ES p _ _ <- get
          b <- lift $ goalAtFocus (fst p)
          return $! (binderTy b)

is_guess :: Elab' aux Bool
is_guess = do ES p _ _ <- get
              b <- lift $ goalAtFocus (fst p)
              case b of
                   Guess _ _ -> return True
                   _ -> return False

-- | Get the guess at the current hole, if there is one
get_guess :: Elab' aux Term
get_guess = do ES p _ _ <- get
               b <- lift $ goalAtFocus (fst p)
               case b of
                    Guess t v -> return $! v
                    _ -> fail "Not a guess"

-- | Typecheck locally
get_type :: Raw -> Elab' aux Type
get_type tm = do ctxt <- get_context
                 env <- get_env
                 (val, ty) <- lift $ check ctxt env tm
                 return $! (finalise ty)

get_type_val :: Raw -> Elab' aux (Term, Type)
get_type_val tm = do ctxt <- get_context
                     env <- get_env
                     (val, ty) <- lift $ check ctxt env tm
                     return $! (finalise val, finalise ty)

-- | get holes we've deferred for later definition
get_deferred :: Elab' aux [Name]
get_deferred = do ES p _ _ <- get
                  return $! (deferred (fst p))

checkInjective :: (Term, Term, Term) -> Elab' aux ()
checkInjective (tm, l, r) = do ctxt <- get_context
                               if isInj ctxt tm then return $! ()
                                else lift $ tfail (NotInjective tm l r)
  where isInj ctxt (P _ n _)
            | isConName n ctxt = True
        isInj ctxt (App _ f a) = isInj ctxt f
        isInj ctxt (Constant _) = True
        isInj ctxt (TType _) = True
        isInj ctxt (Bind _ (Pi _ _ _ _) sc) = True
        isInj ctxt _ = False

-- | get implementation argument names
get_implementations :: Elab' aux [Name]
get_implementations = do ES p _ _ <- get
                         return $! (implementations (fst p))

-- | get auto argument names
get_autos :: Elab' aux [(Name, ([FailContext], [Name]))]
get_autos = do ES p _ _ <- get
               return $! (autos (fst p))

-- | given a desired hole name, return a unique hole name
unique_hole :: Name -> Elab' aux Name
unique_hole = unique_hole' False

unique_hole' :: Bool -> Name -> Elab' aux Name
unique_hole' reusable n
      = do ES p _ _ <- get
           let bs = bound_in (pterm (fst p)) ++
                    bound_in_term (ptype (fst p))
           let nouse = holes (fst p) ++ bs ++ dontunify (fst p) ++ usedns (fst p)
           n' <- return $! uniqueNameCtxt (context (fst p)) n nouse
           ES (p, a) s u <- get
           case n' of
                MN i _ -> when (i >= nextname p) $
                            put (ES (p { nextname = i + 1 }, a) s u)
                _ -> return $! ()
           return $! n'

elog :: String -> Elab' aux ()
elog str = do ES p logs prev <- get
              put (ES p (logs ++ str ++ "\n") prev)

getLog :: Elab' aux String
getLog = do ES p logs _ <- get
            return $! logs

-- The primitives, from ProofState

attack :: Elab' aux ()
attack = processTactic' Attack

claim :: Name -> Raw -> Elab' aux ()
claim n t = processTactic' (Claim n t)

claimFn :: Name -> Name -> Raw -> Elab' aux ()
claimFn n bn t = processTactic' (ClaimFn n bn t)

unifyGoal :: Raw -> Elab' aux ()
unifyGoal t = processTactic' (UnifyGoal t)

unifyTerms :: Raw -> Raw -> Elab' aux ()
unifyTerms t1 t2 = processTactic' (UnifyTerms t1 t2)

exact :: Raw -> Elab' aux ()
exact t = processTactic' (Exact t)

fill :: Raw -> Elab' aux ()
fill t = processTactic' (Fill t)

match_fill :: Raw -> Elab' aux ()
match_fill t = processTactic' (MatchFill t)

prep_fill :: Name -> [Name] -> Elab' aux ()
prep_fill n ns = processTactic' (PrepFill n ns)

complete_fill :: Elab' aux ()
complete_fill = processTactic' CompleteFill

solve :: Elab' aux ()
solve = processTactic' Solve

start_unify :: Name -> Elab' aux ()
start_unify n = processTactic' (StartUnify n)

end_unify :: Elab' aux ()
end_unify = processTactic' EndUnify

-- Clear the list of variables not to unify, and try to solve them
unify_all :: Elab' aux ()
unify_all = processTactic' UnifyAll

regret :: Elab' aux ()
regret = processTactic' Regret

compute :: Elab' aux ()
compute = processTactic' Compute

computeLet :: Name -> Elab' aux ()
computeLet n = processTactic' (ComputeLet n)

simplify :: Elab' aux ()
simplify = processTactic' Simplify

whnf_compute :: Elab' aux ()
whnf_compute = processTactic' WHNF_Compute

whnf_compute_args :: Elab' aux ()
whnf_compute_args = processTactic' WHNF_ComputeArgs

eval_in :: Raw -> Elab' aux ()
eval_in t = processTactic' (EvalIn t)

check_in :: Raw -> Elab' aux ()
check_in t = processTactic' (CheckIn t)

intro :: Maybe Name -> Elab' aux ()
intro n = processTactic' (Intro n)

introTy :: Raw -> Maybe Name -> Elab' aux ()
introTy ty n = processTactic' (IntroTy ty n)

forall :: Name -> RigCount -> Maybe ImplicitInfo -> Raw -> Elab' aux ()
forall n r i t = processTactic' (Forall n r i t)

letbind :: Name -> Raw -> Raw -> Elab' aux ()
letbind n t v = processTactic' (LetBind n t v)

expandLet :: Name -> Term -> Elab' aux ()
expandLet n v = processTactic' (ExpandLet n v)

rewrite :: Raw -> Elab' aux ()
rewrite tm = processTactic' (Rewrite tm)

induction :: Raw -> Elab' aux ()
induction tm = processTactic' (Induction tm)

casetac :: Raw -> Elab' aux ()
casetac tm = processTactic' (CaseTac tm)

equiv :: Raw -> Elab' aux ()
equiv tm = processTactic' (Equiv tm)

-- | Turn the current hole into a pattern variable with the provided
-- name, made unique if not the same as the head of the hole queue
patvar :: Name -> Elab' aux ()
patvar n@(SN _) = do apply (Var n) []; solve
patvar n = do env <- get_env
              hs <- get_holes
              if (n `elem` map fstEnv env) then do apply (Var n) []; solve
                else do n' <- case hs of
                                   (h : hs) -> if n == h then return n
                                                  else unique_hole n
                                   _ -> unique_hole n
                        processTactic' (PatVar n)

-- | Turn the current hole into a pattern variable with the provided
-- name, but don't make MNs unique.
patvar' :: Name -> Elab' aux ()
patvar' n@(SN _) = do apply (Var n) [] ; solve
patvar' n = do env <- get_env
               hs <- get_holes
               if (n `elem` map fstEnv env) then do apply (Var n) [] ; solve
                  else processTactic' (PatVar n)

patbind :: Name -> RigCount -> Elab' aux ()
patbind n r = processTactic' (PatBind n r)

focus :: Name -> Elab' aux ()
focus n = processTactic' (Focus n)

movelast :: Name -> Elab' aux ()
movelast n = processTactic' (MoveLast n)

dotterm :: Elab' aux ()
dotterm = do ES (p, a) s m <- get
             tm <- get_term
             case holes p of
                  [] -> return ()
                  (h : hs) ->
                     do let outer = findOuter h [] tm
                        let p' = p { dotted = (h, outer) : dotted p }
--                         trace ("DOTTING " ++ show (h, outer) ++ "\n" ++
--                                show tm) $
                        put $ ES (p', a) s m
 where
  findOuter h env (P _ n _) | h == n = env
  findOuter h env (Bind n b sc)
      = union (foB b)
              (findOuter h env (instantiate (P Bound n (binderTy b)) sc))
     where foB (Guess t v) = union (findOuter h env t) (findOuter h (n:env) v)
           foB (Let t v) = union (findOuter h env t) (findOuter h env v)
           foB b = findOuter h env (binderTy b)
  findOuter h env (App _ f a)
      = union (findOuter h env f) (findOuter h env a)
  findOuter h env _ = []


get_dotterm :: Elab' aux [(Name, [Name])]
get_dotterm = do ES (p, a) s m <- get
                 return (dotted p)

-- | Set the zipper in the proof state to point at the current sub term
-- (This currently happens automatically, so this will have no effect...)
zipHere :: Elab' aux ()
zipHere = do ES (ps, a) s m <- get
             let pt' = refocus (Just (head (holes ps))) (pterm ps)
             put (ES (ps { pterm = pt' }, a) s m)

matchProblems :: Bool -> Elab' aux ()
matchProblems all = processTactic' (MatchProblems all)

unifyProblems :: Elab' aux ()
unifyProblems = processTactic' UnifyProblems

defer :: [Name] -> Name -> Elab' aux Name
defer ds n = do n' <- unique_hole n
                processTactic' (Defer ds n')
                return n'

deferType :: Name -> Raw -> [Name] -> Elab' aux ()
deferType n ty ns = processTactic' (DeferType n ty ns)

implementationArg :: Name -> Elab' aux ()
implementationArg n = processTactic' (Implementation n)

autoArg :: Name -> Elab' aux ()
autoArg n = processTactic' (AutoArg n)

setinj :: Name -> Elab' aux ()
setinj n = processTactic' (SetInjective n)

proofstate :: Elab' aux ()
proofstate = processTactic' ProofState

reorder_claims :: Name -> Elab' aux ()
reorder_claims n = processTactic' (Reorder n)

qed :: Elab' aux Term
qed = do processTactic' QED
         ES p _ _ <- get
         return $! (getProofTerm (pterm (fst p)))

undo :: Elab' aux ()
undo = processTactic' Undo

-- | Prepare to apply a function by creating holes to be filled by the arguments
prepare_apply :: Raw    -- ^ The operation being applied
              -> [Bool] -- ^ Whether arguments are implicit
              -> Elab' aux [(Name, Name)] -- ^ The names of the arguments and their holes to be filled with elaborated argument values
prepare_apply fn imps =
    do ty <- get_type fn
       ctxt <- get_context
       env <- get_env
       -- let claims = getArgs ty imps
       -- claims <- mkClaims (normalise ctxt env ty) imps []
       -- Count arguments to check if we need to normalise the type
       let usety = if argsOK (finalise ty) imps
                      then finalise ty
                      else normalise ctxt env (finalise ty)
       claims <- -- trace (show (fn, imps, ty, map fst env, normalise ctxt env (finalise ty))) $
                 mkClaims usety imps [] (map fstEnv env)
       ES (p, a) s prev <- get
       -- reverse the claims we made so that args go left to right
       let n = length (filter not imps)
       let (h : hs) = holes p
       put (ES (p { holes = h : (reverse (take n hs) ++ drop n hs) }, a) s prev)
       return $! claims
  where
    argsOK :: Type -> [a] -> Bool
    argsOK (Bind n (Pi _ _ _ _) sc) (i : is) = argsOK sc is
    argsOK _ (i : is) = False
    argsOK _ [] = True

    mkClaims :: Type   -- ^ The type of the operation being applied
             -> [Bool] -- ^ Whether the arguments are implicit
             -> [(Name, Name)] -- ^ Accumulator for produced claims
             -> [Name] -- ^ Hypotheses
             -> Elab' aux [(Name, Name)] -- ^ The names of the arguments and their holes, resp.
    mkClaims (Bind n' (Pi _ _ t_in _) sc) (i : is) claims hs =
        do let t = rebind hs t_in
           n <- getNameFrom (mkMN n')
--            when (null claims) (start_unify n)
           let sc' = instantiate (P Bound n t) sc
           env <- get_env
           claim n (forgetEnv (map fstEnv env) t)
           when i (movelast n)
           mkClaims sc' is ((n', n) : claims) hs
    mkClaims t [] claims _ = return $! (reverse claims)
    mkClaims _ _ _ _
            | Var n <- fn
                   = do ctxt <- get_context
                        lift $ tfail $ TooManyArguments n
            | otherwise = fail $ "Too many arguments for " ++ show fn

    doClaim ((i, _), n, t) = do claim n t
                                when i (movelast n)

    mkMN n@(MN i _) = n
    mkMN n@(UN x) = MN 99999 x
    mkMN n@(SN s) = sMN 99999 (show s)
    mkMN (NS n xs) = NS (mkMN n) xs

    rebind hs (Bind n t sc)
        | n `elem` hs = let n' = uniqueName n hs in
                            Bind n' (fmap (rebind hs) t) (rebind (n':hs) sc)
        | otherwise = Bind n (fmap (rebind hs) t) (rebind (n:hs) sc)
    rebind hs (App s f a) = App s (rebind hs f) (rebind hs a)
    rebind hs t = t

-- | Apply an operator, solving some arguments by unification or matching.
apply, match_apply :: Raw -- ^ The operator to apply
                   -> [(Bool, Int)] -- ^ For each argument, whether to
                                    -- attempt to solve it and the
                                    -- priority in which to do so
                   -> Elab' aux [(Name, Name)]
apply = apply' fill
match_apply = apply' match_fill

apply' :: (Raw -> Elab' aux ()) -> Raw -> [(Bool, Int)] -> Elab' aux [(Name, Name)]
apply' fillt fn imps =
    do args <- prepare_apply fn (map fst imps)
       -- _Don't_ solve the arguments we're specifying by hand.
       -- (remove from unified list before calling end_unify)
       hs <- get_holes
       ES (p, a) s prev <- get
       let dont = if null imps
                     then head hs : dontunify p
                     else getNonUnify (head hs : dontunify p) imps args
       let (n, hunis) = -- trace ("AVOID UNIFY: " ++ show (fn, dont)) $
                        unified p
       let unify = -- trace ("Not done " ++ show hs) $
                   dropGiven dont hunis hs
       let notunify = -- trace ("Not done " ++ show (hs, hunis)) $
                      keepGiven dont hunis hs
       put (ES (p { dontunify = dont, unified = (n, unify),
                    notunified = notunify ++ notunified p }, a) s prev)
       fillt (raw_apply fn (map (Var . snd) args))
       ulog <- getUnifyLog
       g <- goal
       traceWhen ulog
                 ("Goal " ++ show g ++ " -- when elaborating " ++ show fn)
                 end_unify
       return $! (map (\(argName, argHole) -> (argName, updateUnify unify argHole)) args)
  where updateUnify us n = case lookup n us of
                                Just (P _ t _) -> t
                                _ -> n

        getNonUnify acc []     _      = acc
        getNonUnify acc _      []     = acc
        getNonUnify acc ((i,_):is) ((a, t):as)
           | i = getNonUnify acc is as
           | otherwise = getNonUnify (t : acc) is as

--         getNonUnify imps args = map fst (filter (not . snd) (zip (map snd args) (map fst imps)))


apply2 :: Raw -> [Maybe (Elab' aux ())] -> Elab' aux ()
apply2 fn elabs =
    do args <- prepare_apply fn (map isJust elabs)
       fill (raw_apply fn (map (Var . snd) args))
       elabArgs (map snd args) elabs
       ES (p, a) s prev <- get
       let (n, hs) = unified p
       end_unify
       solve
  where elabArgs [] [] = return $! ()
        elabArgs (n:ns) (Just e:es) = do focus n; e
                                         elabArgs ns es
        elabArgs (n:ns) (_:es) = elabArgs ns es

        isJust (Just _) = False
        isJust _        = True

apply_elab :: Name -> [Maybe (Int, Elab' aux ())] -> Elab' aux ()
apply_elab n args =
    do ty <- get_type (Var n)
       ctxt <- get_context
       env <- get_env
       claims <- doClaims (normalise ctxt env ty) args []
       prep_fill n (map fst claims)
       let eclaims = sortBy (\ (_, x) (_,y) -> priOrder x y) claims
       elabClaims [] False claims
       complete_fill
       end_unify
  where
    priOrder Nothing Nothing = EQ
    priOrder Nothing _ = LT
    priOrder _ Nothing = GT
    priOrder (Just (x, _)) (Just (y, _)) = compare x y

    doClaims (Bind n' (Pi _ _ t _) sc) (i : is) claims =
        do n <- unique_hole (mkMN n')
           when (null claims) (start_unify n)
           let sc' = instantiate (P Bound n t) sc
           claim n (forget t)
           case i of
               Nothing -> return $! ()
               Just _ -> -- don't solve by unification as there is an explicit value
                         do ES (p, a) s prev <- get
                            put (ES (p { dontunify = n : dontunify p }, a) s prev)
           doClaims sc' is ((n, i) : claims)
    doClaims t [] claims = return $! (reverse claims)
    doClaims _ _ _ = fail $ "Wrong number of arguments for " ++ show n

    elabClaims failed r []
        | null failed = return $! ()
        | otherwise = if r then elabClaims [] False failed
                           else return $! ()
    elabClaims failed r ((n, Nothing) : xs) = elabClaims failed r xs
    elabClaims failed r (e@(n, Just (_, elaboration)) : xs)
        | r = try (do ES p _ _ <- get
                      focus n; elaboration; elabClaims failed r xs)
                  (elabClaims (e : failed) r xs)
        | otherwise = do ES p _ _ <- get
                         focus n; elaboration; elabClaims failed r xs

    mkMN n@(MN _ _) = n
    mkMN n@(UN x) = MN 0 x
    mkMN (NS n ns) = NS (mkMN n) ns

-- If the goal is not a Pi-type, invent some names and make it a pi type
checkPiGoal :: Name -> Elab' aux ()
checkPiGoal n
            = do g <- goal
                 ctxt <- get_context
                 env <- get_env
                 case (normalise ctxt env g) of
                    Bind _ (Pi _ _ _ _) _ -> return ()
                    _ -> do a <- getNameFrom (sMN 0 "__pargTy")
                            b <- getNameFrom (sMN 0 "__pretTy")
                            f <- getNameFrom (sMN 0 "pf")
                            claim a RType
                            claim b RType
                            claim f (RBind n (Pi RigW Nothing (Var a) RType) (Var b))
                            movelast a
                            movelast b
                            fill (Var f)
                            solve
                            focus f

simple_app :: Bool -> Elab' aux () -> Elab' aux () -> String -> Elab' aux ()
simple_app infer fun arg str =
    try (dep_app fun arg str)
        (infer_app infer fun arg str)

infer_app :: Bool -> Elab' aux () -> Elab' aux () -> String -> Elab' aux ()
infer_app infer fun arg str =
    do a <- getNameFrom (sMN 0 "__argTy")
       b <- getNameFrom (sMN 0 "__retTy")
       f <- getNameFrom (sMN 0 "f")
       s <- getNameFrom (sMN 0 "is")
       claim a RType
       claim b RType
       claim f (RBind (sMN 0 "_aX") (Pi RigW Nothing (Var a) RType) (Var b))
       tm <- get_term
       start_unify s
       -- if 'infer' is set, we're assuming it's a simply typed application
       -- so safe to unify with the goal type (as there'll be no dependencies)
       when infer $ unifyGoal (Var b)
       hs <- get_holes
       claim s (Var a)
       prep_fill f [s]
       focus f; fun
       focus s; arg
       tm <- get_term
       ps <- get_probs
       ty <- goal
       hs <- get_holes
       complete_fill
       env <- get_env
       -- We don't need a and b in the hole queue any more since they were
       -- just for checking f, so move them to the end. If they never end up
       -- getting solved, we'll get an 'Incomplete term' error.
       hs <- get_holes
       when (a `elem` hs) $ do movelast a
       when (b `elem` hs) $ do movelast b
       end_unify

dep_app :: Elab' aux () -> Elab' aux () -> String -> Elab' aux ()
dep_app fun arg str =
    do a <- getNameFrom (sMN 0 "__argTy")
       b <- getNameFrom (sMN 0 "__retTy")
       fty <- getNameFrom (sMN 0 "__fnTy")
       f <- getNameFrom (sMN 0 "f")
       s <- getNameFrom (sMN 0 "ds")
       claim a RType
       claim fty RType
       claim f (Var fty)
       tm <- get_term
       g <- goal
       start_unify s
       claim s (Var a)

       prep_fill f [s]
       focus f; attack; fun
       end_unify
       fty <- goal
       solve
       focus s; attack;
       ctxt <- get_context
       env <- get_env
       case normalise ctxt env fty of
            -- if f gives a function type, unify our argument type with
            -- f's expected argument type
            Bind _ (Pi _ _ argty _) _ -> unifyGoal (forget argty)
            -- Can't infer a type for 'f', so fail here (and drop back to
            -- simply typed application where we infer the type for f)
            _ -> fail "Can't make type"
       end_unify
       arg
       solve
       complete_fill

       -- We don't need a and b in the hole queue any more since they were
       -- just for checking f, so move them to the end. If they never end up
       -- getting solved, we'll get an 'Incomplete term' error.
       hs <- get_holes
       when (a `elem` hs) $ do movelast a
       when (b `elem` hs) $ do movelast b
       end_unify

-- Abstract over an argument of unknown type, giving a name for the hole
-- which we'll fill with the argument type too.
arg :: Name -> RigCount -> Maybe ImplicitInfo -> Name -> Elab' aux ()
arg n r i tyhole = do ty <- unique_hole tyhole
                      claim ty RType
                      movelast ty
                      forall n r i (Var ty)

-- try a tactic, if it adds any unification problem, return an error
no_errors :: Elab' aux () -> Maybe Err -> Elab' aux ()
no_errors tac err
       = do ps <- get_probs
            s <- get
            case err of
                 Nothing -> tac
                 Just e -> -- update the error, if there is one.
                     case runStateT tac s of
                          Error _ -> lift $ Error e
                          OK (a, s') -> do put s'
                                           return a
            unifyProblems
            ps' <- get_probs
            if (length ps' > length ps) then
               case reverse ps' of
                    ((x, y, _, env, inerr, while, _) : _) ->
                       let (xp, yp) = getProvenance inerr
                           env' = map (\(x, rig, b) -> (x, binderTy b)) env in
                                  lift $ tfail $
                                         case err of
                                              Nothing -> CantUnify False (x, xp) (y, yp) inerr env' 0
                                              Just e -> e
               else return $! ()

-- Try a tactic, if it fails, try another
try :: Elab' aux a -> Elab' aux a -> Elab' aux a
try t1 t2 = try' t1 t2 False

handleError :: (Err -> Bool) -> Elab' aux a -> Elab' aux a -> Elab' aux a
handleError p t1 t2
          = do s <- get
               ps <- get_probs
               case runStateT t1 s of
                    OK (v, s') -> do put s'
                                     return $! v
                    Error e1 -> if p e1 then
                                   do case runStateT t2 s of
                                         OK (v, s') -> do put s'; return $! v
                                         Error e2 -> lift (tfail e2)
                                   else lift (tfail e1)

try' :: Elab' aux a -> Elab' aux a -> Bool -> Elab' aux a
try' t1 t2 proofSearch
  = do s <- get
       ps <- get_probs
       ulog <- getUnifyLog
       ivs <- get_implementations
       case prunStateT 999999 False ps Nothing t1 s of
            OK ((v, _, _), s') -> do put s'
                                     return $! v
            Error e1 -> traceWhen ulog ("try failed " ++ show e1) $
                         if recoverableErr e1 then
                            do case runStateT t2 s of
                                 OK (v, s') -> do put s'; return $! v
                                 Error e2 -> lift (tfail e2)
                           else lift (tfail e1)
  where recoverableErr err@(CantUnify r x y _ _ _)
             = -- traceWhen r (show err) $
               r || proofSearch
        recoverableErr (CantSolveGoal _ _) = False
        recoverableErr (CantResolveAlts _) = proofSearch
        recoverableErr (ProofSearchFail (Msg _)) = True
        recoverableErr (ProofSearchFail _) = False
        recoverableErr (ElaboratingArg _ _ _ e) = recoverableErr e
        recoverableErr (At _ e) = recoverableErr e
        recoverableErr (ElabScriptDebug _ _ _) = False
        recoverableErr _ = True

tryCatch :: Elab' aux a -> (Err -> Elab' aux a) -> Elab' aux a
tryCatch t1 t2
  = do s <- get
       ps <- get_probs
       ulog <- getUnifyLog
--        case prunStateT 999999 False ps t1 s of
       case runStateT t1 s of
            OK (v, s') -> do put s'
                             return $! v
            Error e1 -> traceWhen ulog ("tryCatch failed " ++ show e1) $
                          case runStateT (t2 e1) s of
                               OK (v, s') -> do put s'
                                                return $! v
                               Error e2 -> lift (tfail e2)

tryWhen :: Bool -> Elab' aux a -> Elab' aux a -> Elab' aux a
tryWhen True a b = try a b
tryWhen False a b = a

-- Bool says whether it's okay to create new unification problems. If set
-- to False, then the whole tactic fails if there are any new problems
tryAll :: [(Elab' aux a, Name)] -> Elab' aux a
tryAll = tryAll' True

tryAll' :: Bool -> [(Elab' aux a, Name)] -> Elab' aux a
tryAll' _ [(x, _)] = x
tryAll' constrok xs = doAll [] 999999 xs
  where
    cantResolve :: Elab' aux a
    cantResolve = lift $ tfail $ CantResolveAlts (map snd xs)

    noneValid :: Elab' aux a
    noneValid = lift $ tfail $ NoValidAlts (map snd xs)

    doAll :: [Elab' aux a] -> -- successes
             Int -> -- most problems
             [(Elab' aux a, Name)] -> -- still to try
             Elab' aux a
    doAll [res] pmax [] = res
    doAll (_:_) pmax [] = cantResolve
    doAll [] pmax    [] = noneValid
    doAll cs pmax    ((x, msg):xs)
       = do s <- get
            ps <- get_probs
            ivs <- get_implementations
            g <- goal
            case prunStateT pmax True ps (if constrok then Nothing
                                                      else Just ivs) x s of
                OK ((v, newps, probs), s') ->
                      do let cs' = if (newps < pmax)
                                      then [do put s'; return $! v]
                                      else (do put s'; return $! v) : cs
                         put s
                         doAll cs' newps xs
                Error err -> do put s
                                doAll cs pmax xs

-- Run an elaborator, and fail if any problems or constraints are introduced
prunStateT
  :: Int
     -> Bool
     -> [a]
     -> Maybe [b] -- constraints left, if we're interested
     -> Control.Monad.State.Strict.StateT
          (ElabState t) TC t1
     -> ElabState t
     -> TC ((t1, Int, Idris.Core.Unify.Fails), ElabState t)
prunStateT pmax zok ps ivs x s
      = case runStateT x s of
             OK (v, s'@(ES (p, _) _ _)) ->
                 let newps = length (problems p) - length ps
                     ibad = badImplementations (implementations p) ivs
                     newpmax = if newps < 0 then 0 else newps in
                 if (newpmax > pmax || (not zok && newps > 0)) -- length ps == 0 && newpmax > 0))
                    then case reverse (problems p) of
                            ((_,_,_,_,e,_,_):_) -> Error e
                    else if ibad
                            then Error (InternalMsg "Constraint introduced in disambiguation")
                            else OK ((v, newpmax, problems p), s')
             Error e -> Error e
  where
    badImplementations _ Nothing = False
    badImplementations inow (Just ithen) = length inow > length ithen

debugElaborator :: [ErrorReportPart] -> Elab' aux a
debugElaborator msg = do ps <- fmap proof get
                         saveState -- so we don't need to remember the hole order
                         hs <- get_holes
                         holeInfo <- mapM getHoleInfo hs
                         loadState
                         lift . Error $ ElabScriptDebug msg (getProofTerm (pterm ps)) holeInfo
  where getHoleInfo :: Name -> Elab' aux (Name, Type, [(Name, Binder Type)])
        getHoleInfo h = do focus h
                           g <- goal
                           env <- get_env
                           return (h, g, envBinders env)

qshow :: Fails -> String
qshow fs = show (map (\ (x, y, _, _, _, _, _) -> (x, y)) fs)

dumpprobs [] = ""
dumpprobs ((_,_,_,e):es) = show e ++ "\n" ++ dumpprobs es

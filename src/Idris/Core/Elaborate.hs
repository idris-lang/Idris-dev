{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, PatternGuards #-}

{- A high level language of tactic composition, for building
   elaborators from a high level language into the core theory.

   This is our interface to proof construction, rather than
   ProofState, because this gives us a language to build derived
   tactics out of the primitives.
-}

module Idris.Core.Elaborate(module Idris.Core.Elaborate,
                            module Idris.Core.ProofState) where

import Idris.Core.ProofState
import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.Typecheck
import Idris.Core.Unify
import Idris.Core.DeepSeq

import Control.DeepSeq
import Control.Monad.State.Strict
import Data.Char
import Data.List
import Debug.Trace

import Util.Pretty

-- I don't really want this here, but it's useful for the test shell
data Command = Theorem Name Raw
             | Eval Raw
             | Quit
             | Print Name
             | Tac (Elab ())

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

saveState :: Elab' aux ()
saveState = do e@(ES p s _) <- get
               put (ES p s (Just e))

loadState :: Elab' aux ()
loadState = do (ES p s e) <- get
               case e of
                  Just st -> put st
                  _ -> fail "Nothing to undo"

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
                   return $! n'

setNextName :: Elab' aux ()
setNextName = do env <- get_env
                 ES (p, a) s e <- get
                 let pargs = map fst (getArgTys (ptype p))
                 initNextNameFrom (pargs ++ map fst env)

initNextNameFrom :: [Name] -> Elab' aux ()
initNextNameFrom ns = do ES (p, a) s e <- get
                         let n' = maxName (nextname p) ns 
                         put (ES (p { nextname = n' }, a) s e)
  where
    maxName m ((MN i _) : xs) = maxName (max m i) xs
    maxName m (_ : xs) = maxName m xs
    maxName m [] = m + 1

errAt :: String -> Name -> Elab' aux a -> Elab' aux a
errAt thing n elab = do s <- get
                        case runStateT elab s of
                             OK (a, s') -> do put s'
                                              return $! a
                             Error (At f e) ->
                                 lift $ Error (At f (Elaborating thing n e))
                             Error e -> lift $ Error (Elaborating thing n e)

erun :: FC -> Elab' aux a -> Elab' aux a
erun f elab = do s <- get
                 case runStateT elab s of
                    OK (a, s')     -> do put s'
                                         return $! a
                    Error (ProofSearchFail (At f e))
                                   -> lift $ Error (ProofSearchFail (At f e))
                    Error (At f e) -> lift $ Error (At f e)
                    Error e        -> lift $ Error (At f e)

runElab :: aux -> Elab' aux a -> ProofState -> TC (a, ElabState aux)
runElab a e ps = runStateT e (ES (ps, a) "" Nothing)

execElab :: aux -> Elab' aux a -> ProofState -> TC (ElabState aux)
execElab a e ps = execStateT e (ES (ps, a) "" Nothing)

initElaborator :: Name -> Context -> Type -> ProofState
initElaborator = newProof

elaborate :: Context -> Name -> Type -> aux -> Elab' aux a -> TC (a, String)
elaborate ctxt n ty d elab = do let ps = initElaborator n ctxt ty
                                (a, ES ps' str _) <- runElab d elab ps
                                return $! (a, str)

force_term :: Elab' aux ()
force_term = do ES (ps, a) l p <- get
                put (ES (ps { pterm = force (pterm ps) }, a) l p)

updateAux :: (aux -> aux) -> Elab' aux ()
updateAux f = do ES (ps, a) l p <- get
                 put (ES (ps, f a) l p)

getAux :: Elab' aux aux
getAux = do ES (ps, a) _ _ <- get
            return $! a

unifyLog :: Bool -> Elab' aux ()
unifyLog log = do ES (ps, a) l p <- get
                  put (ES (ps { unifylog = log }, a) l p)

getUnifyLog :: Elab' aux Bool
getUnifyLog = do ES (ps, a) l p <- get
                 return (unifylog ps)

processTactic' t = do ES (p, a) logs prev <- get
                      (p', log) <- lift $ processTactic t p
                      put (ES (p', a) (logs ++ log) prev)
                      return $! ()

-- Some handy gadgets for pulling out bits of state

-- get the global context
get_context :: Elab' aux Context
get_context = do ES p _ _ <- get
                 return $! (context (fst p))

-- update the context
-- (should only be used for adding temporary definitions or all sorts of
--  stuff could go wrong)
set_context :: Context -> Elab' aux ()
set_context ctxt = do ES (p, a) logs prev <- get
                      put (ES (p { context = ctxt }, a) logs prev)

-- get the proof term
get_term :: Elab' aux Term
get_term = do ES p _ _ <- get
              return $! (pterm (fst p))

-- get the proof term
update_term :: (Term -> Term) -> Elab' aux ()
update_term f = do ES (p,a) logs prev <- get
                   let p' = p { pterm = f (pterm p) }
                   put (ES (p', a) logs prev)

-- get the local context at the currently in focus hole
get_env :: Elab' aux Env
get_env = do ES p _ _ <- get
             lift $ envAtFocus (fst p)

get_holes :: Elab' aux [Name]
get_holes = do ES p _ _ <- get
               return $! (holes (fst p))

get_probs :: Elab' aux Fails
get_probs = do ES p _ _ <- get
               return $! (problems (fst p))

-- get the current goal type
goal :: Elab' aux Type
goal = do ES p _ _ <- get
          b <- lift $ goalAtFocus (fst p)
          return $! (binderTy b)

-- Get the guess at the current hole, if there is one
get_guess :: Elab' aux Type
get_guess = do ES p _ _ <- get
               b <- lift $ goalAtFocus (fst p)
               case b of
                    Guess t v -> return $! v
                    _ -> fail "Not a guess"

-- typecheck locally
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

-- get holes we've deferred for later definition
get_deferred :: Elab' aux [Name]
get_deferred = do ES p _ _ <- get
                  return $! (deferred (fst p))

checkInjective :: (Term, Term, Term) -> Elab' aux ()
checkInjective (tm, l, r) = do ctxt <- get_context
                               if isInj ctxt tm then return $! ()
                                else lift $ tfail (NotInjective tm l r)
  where isInj ctxt (P _ n _)
            | isConName n ctxt = True
        isInj ctxt (App f a) = isInj ctxt f
        isInj ctxt (Constant _) = True
        isInj ctxt (TType _) = True
        isInj ctxt (Bind _ (Pi _) sc) = True
        isInj ctxt _ = False

-- get instance argument names
get_instances :: Elab' aux [Name]
get_instances = do ES p _ _ <- get
                   return $! (instances (fst p))

-- given a desired hole name, return a unique hole name
unique_hole = unique_hole' False

unique_hole' :: Bool -> Name -> Elab' aux Name
unique_hole' reusable n
      = do ES p _ _ <- get
           let bs = bound_in (pterm (fst p)) ++
                    bound_in (ptype (fst p))
           let nouse = holes (fst p) ++ bs ++ dontunify (fst p) ++ usedns (fst p)
           n' <- return $! uniqueNameCtxt (context (fst p)) n nouse
           ES (p, a) s u <- get
           case n' of
                MN i _ -> when (i >= nextname p) $
                            put (ES (p { nextname = i + 1 }, a) s u)
                _ -> return $! ()
           return $! n'
  where
    bound_in (Bind n b sc) = n : bi b ++ bound_in sc
      where
        bi (Let t v) = bound_in t ++ bound_in v
        bi (Guess t v) = bound_in t ++ bound_in v
        bi b = bound_in (binderTy b)
    bound_in (App f a) = bound_in f ++ bound_in a
    bound_in _ = []

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

regret :: Elab' aux ()
regret = processTactic' Regret

compute :: Elab' aux ()
compute = processTactic' Compute

computeLet :: Name -> Elab' aux ()
computeLet n = processTactic' (ComputeLet n)

simplify :: Elab' aux ()
simplify = processTactic' Simplify

hnf_compute :: Elab' aux ()
hnf_compute = processTactic' HNF_Compute

eval_in :: Raw -> Elab' aux ()
eval_in t = processTactic' (EvalIn t)

check_in :: Raw -> Elab' aux ()
check_in t = processTactic' (CheckIn t)

intro :: Maybe Name -> Elab' aux ()
intro n = processTactic' (Intro n)

introTy :: Raw -> Maybe Name -> Elab' aux ()
introTy ty n = processTactic' (IntroTy ty n)

forall :: Name -> Raw -> Elab' aux ()
forall n t = processTactic' (Forall n t)

letbind :: Name -> Raw -> Raw -> Elab' aux ()
letbind n t v = processTactic' (LetBind n t v)

expandLet :: Name -> Term -> Elab' aux ()
expandLet n v = processTactic' (ExpandLet n v)

rewrite :: Raw -> Elab' aux ()
rewrite tm = processTactic' (Rewrite tm)

induction :: Name -> Elab' aux ()
induction nm = processTactic' (Induction nm)

equiv :: Raw -> Elab' aux ()
equiv tm = processTactic' (Equiv tm)

patvar :: Name -> Elab' aux ()
patvar n = do env <- get_env
              hs <- get_holes
              if (n `elem` map fst env) then do apply (Var n) []; solve
                else do n' <- case n of
                                    UN _ -> return $! n
                                    MN _ _ -> unique_hole n
                                    NS _ _ -> return $! n
                        processTactic' (PatVar n')

patbind :: Name -> Elab' aux ()
patbind n = processTactic' (PatBind n)

focus :: Name -> Elab' aux ()
focus n = processTactic' (Focus n)

movelast :: Name -> Elab' aux ()
movelast n = processTactic' (MoveLast n)

matchProblems :: Elab' aux ()
matchProblems = processTactic' MatchProblems

unifyProblems :: Elab' aux ()
unifyProblems = processTactic' UnifyProblems

defer :: Name -> Elab' aux ()
defer n = do n' <- unique_hole n
             processTactic' (Defer n')

deferType :: Name -> Raw -> [Name] -> Elab' aux ()
deferType n ty ns = processTactic' (DeferType n ty ns)

instanceArg :: Name -> Elab' aux ()
instanceArg n = processTactic' (Instance n)

setinj :: Name -> Elab' aux ()
setinj n = processTactic' (SetInjective n)

proofstate :: Elab' aux ()
proofstate = processTactic' ProofState

reorder_claims :: Name -> Elab' aux ()
reorder_claims n = processTactic' (Reorder n)

qed :: Elab' aux Term
qed = do processTactic' QED
         ES p _ _ <- get
         return $! (pterm (fst p))

undo :: Elab' aux ()
undo = processTactic' Undo

prepare_apply :: Raw -> [Bool] -> Elab' aux [Name]
prepare_apply fn imps = 
    do ty <- get_type fn
       ctxt <- get_context
       env <- get_env
       -- let claims = getArgs ty imps
       -- claims <- mkClaims (normalise ctxt env ty) imps []
       claims <- mkClaims (finalise ty) imps [] (map fst env)
       ES (p, a) s prev <- get
       -- reverse the claims we made so that args go left to right
       let n = length (filter not imps)
       let (h : hs) = holes p
       put (ES (p { holes = h : (reverse (take n hs) ++ drop n hs) }, a) s prev)
--        case claims of
--             [] -> return ()
--             (h : _) -> reorder_claims h
       return $! claims
  where
    mkClaims (Bind n' (Pi t_in) sc) (i : is) claims hs =
        do let t = rebind hs t_in
           n <- getNameFrom (mkMN n')
--            when (null claims) (start_unify n)
           let sc' = instantiate (P Bound n t) sc
--            trace ("CLAIMING " ++ show (n, t) ++ " with " ++ show (fn, hs)) $
           claim n (forget t)
           when i (movelast n)
           mkClaims sc' is (n : claims) hs
    mkClaims t [] claims _ = return $! (reverse claims)
    mkClaims _ _ _ _
            | Var n <- fn
                   = do ctxt <- get_context
                        case lookupTy n ctxt of
                                [] -> lift $ tfail $ NoSuchVariable n
                                _ -> lift $ tfail $ TooManyArguments n
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
    rebind hs (App f a) = App (rebind hs f) (rebind hs a)
    rebind hs t = t

apply, match_apply :: Raw -> [(Bool, Int)] -> Elab' aux [Name]
apply = apply' fill
match_apply = apply' match_fill

apply' :: (Raw -> Elab' aux ()) -> Raw -> [(Bool, Int)] -> Elab' aux [Name]
apply' fillt fn imps =
    do args <- prepare_apply fn (map fst imps)
       -- _Don't_ solve the arguments we're specifying by hand.
       -- (remove from unified list before calling end_unify)
       -- HMMM: Actually, if we get it wrong, the typechecker will complain!
       -- so do nothing
       hs <- get_holes
       ES (p, a) s prev <- get
       let dont = head hs : dontunify p ++
                          if null imps then [] -- do all we can
                             else
                             map fst (filter (not.snd) (zip args (map fst imps)))
       let (n, hunis) = -- trace ("AVOID UNIFY: " ++ show (fn, dont) ++ "\n" ++ show ptm) $
                        unified p
       let unify = -- trace ("Not done " ++ show hs) $
                   dropGiven dont hunis hs
       let notunify = -- trace ("Not done " ++ show hs) $
                       keepGiven dont hunis hs
       put (ES (p { dontunify = dont, unified = (n, unify),
                    notunified = notunify ++ notunified p }, a) s prev)
       fillt (raw_apply fn (map Var args))
--        trace ("Goal " ++ show g ++ "\n" ++ show (fn,  imps, unify) ++ "\n" ++ show ptm) $
       end_unify
       return $! (map (updateUnify unify) args)
  where updateUnify us n = case lookup n us of
                                Just (P _ t _) -> t
                                _ -> n

apply2 :: Raw -> [Maybe (Elab' aux ())] -> Elab' aux ()
apply2 fn elabs =
    do args <- prepare_apply fn (map isJust elabs)
       fill (raw_apply fn (map Var args))
       elabArgs args elabs
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
       claims <- doClaims (hnf ctxt env ty) args []
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

    doClaims (Bind n' (Pi t) sc) (i : is) claims =
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
                 case g of
                    Bind _ (Pi _) _ -> return ()
                    _ -> do a <- getNameFrom (sMN 0 "pargTy")
                            b <- getNameFrom (sMN 0 "pretTy")
                            f <- getNameFrom (sMN 0 "pf")
                            claim a RType
                            claim b RType
                            claim f (RBind n (Pi (Var a)) (Var b))
                            movelast a
                            movelast b
                            fill (Var f)
                            solve
                            focus f

simple_app :: Elab' aux () -> Elab' aux () -> String -> Elab' aux ()
simple_app fun arg appstr =
    do a <- getNameFrom (sMN 0 "argTy")
       b <- getNameFrom (sMN 0 "retTy")
       f <- getNameFrom (sMN 0 "f")
       s <- getNameFrom (sMN 0 "s")
       claim a RType
       claim b RType
       claim f (RBind (sMN 0 "aX") (Pi (Var a)) (Var b))
       tm <- get_term
       start_unify s
       claim s (Var a)
       prep_fill f [s]
       focus f; fun
       focus s; arg
       tm <- get_term
       ps <- get_probs
       complete_fill
       hs <- get_holes
       env <- get_env
       -- We don't need a and b in the hole queue any more since they were
       -- just for checking f, so discard them if they are still there.
       -- If they haven't been solved, regret will fail
       when (a `elem` hs) $ do focus a; regretWith (CantInferType appstr)
       when (b `elem` hs) $ do focus b; regretWith (CantInferType appstr)
       end_unify
  where regretWith err = try regret
                             (lift $ tfail err)

-- Abstract over an argument of unknown type, giving a name for the hole
-- which we'll fill with the argument type too.
arg :: Name -> Name -> Elab' aux ()
arg n tyhole = do ty <- unique_hole tyhole
                  claim ty RType
                  forall n (Var ty)

-- try a tactic, if it adds any unification problem, return an error
no_errors :: Elab' aux () -> Elab' aux ()
no_errors tac
   = do ps <- get_probs
        tac
        ps' <- get_probs
        if (length ps' > length ps) then
           case reverse ps' of
                ((x,y,env,err) : _) ->
                   let env' = map (\(x, b) -> (x, binderTy b)) env in
                              lift $ tfail $ CantUnify False x y err env' 0
           else return $! ()

-- Try a tactic, if it fails, try another
try :: Elab' aux a -> Elab' aux a -> Elab' aux a
try t1 t2 = try' t1 t2 False

try' :: Elab' aux a -> Elab' aux a -> Bool -> Elab' aux a
try' t1 t2 proofSearch
          = do s <- get
               ps <- get_probs
               case prunStateT 999999 False ps t1 s of
                    OK ((v, _), s') -> do put s'
                                          return $! v
                    Error e1 -> if recoverableErr e1 then
                                   do case runStateT t2 s of
                                         OK (v, s') -> do put s'; return $! v
                                         Error e2 -> if score e1 >= score e2
                                                        then lift (tfail e1)
                                                        else lift (tfail e2)
                                   else lift (tfail e1)
  where recoverableErr err@(CantUnify r x y _ _ _)
             = -- traceWhen r (show err) $
               r || proofSearch
        recoverableErr (ProofSearchFail _) = False
        recoverableErr _ = True

tryWhen :: Bool -> Elab' aux a -> Elab' aux a -> Elab' aux a
tryWhen True a b = try a b
tryWhen False a b = a


-- Try a selection of tactics. Exactly one must work, all others must fail
tryAll :: [(Elab' aux a, String)] -> Elab' aux a
tryAll xs = tryAll' [] 999999 (cantResolve, 0) (map fst xs)
  where
    cantResolve :: Elab' aux a
    cantResolve = lift $ tfail $ CantResolveAlts (map snd xs)

    tryAll' :: [Elab' aux a] -> -- successes
               Int -> -- most problems
               (Elab' aux a, Int) -> -- smallest failure
               [Elab' aux a] -> -- still to try
               Elab' aux a
    tryAll' [res] pmax _   [] = res
    tryAll' (_:_) pmax _   [] = cantResolve
    tryAll' [] pmax (f, _) [] = f
    tryAll' cs pmax f (x:xs)
       = do s <- get
            ps <- get_probs
            case prunStateT pmax True ps x s of
                OK ((v, newps), s') ->
                    do let cs' = if (newps < pmax)
                                    then [do put s'; return $! v]
                                    else (do put s'; return $! v) : cs
                       tryAll' cs' newps f xs
                Error err -> do put s
                                if (score err) < 100
                                    then tryAll' cs pmax (better err f) xs
                                    else tryAll' [] pmax (better err f) xs -- give up


    better err (f, i) = let s = score err in
                            if (s >= i) then (lift (tfail err), s)
                                        else (f, i)

prunStateT pmax zok ps x s
      = case runStateT x s of
             OK (v, s'@(ES (p, _) _ _)) ->
                 let newps = length (problems p) - length ps
                     newpmax = if newps < 0 then 0 else newps in
                 if (newpmax > pmax || (not zok && newps > 0)) -- length ps == 0 && newpmax > 0))
                    then case reverse (problems p) of
                            ((_,_,_,e):_) -> Error e
                    else OK ((v, newpmax), s')
             Error e -> Error e

qshow :: Fails -> String
qshow fs = show (map (\ (x, y, _, _) -> (x, y)) fs)

dumpprobs [] = ""
dumpprobs ((_,_,_,e):es) = show e ++ "\n" ++ dumpprobs es

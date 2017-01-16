{-|
Module      : Idris.Core.ProofState
Description : Proof state implementation.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.

Implements a proof state, some primitive tactics for manipulating
proofs, and some high level commands for introducing new theorems,
evaluation/checking inside the proof system, etc.
-}

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PatternGuards #-}
module Idris.Core.ProofState(
    ProofState(..), newProof, envAtFocus, goalAtFocus
  , Tactic(..), Goal(..), processTactic, nowElaboratingPS
  , doneElaboratingAppPS, doneElaboratingArgPS, dropGiven
  , keepGiven, getProvenance
  ) where

import Idris.Core.Evaluate
import Idris.Core.ProofTerm
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Core.Unify
import Idris.Core.WHNF

import Util.Pretty hiding (fill)

import Control.Applicative hiding (empty)
import Control.Arrow ((***))
import Control.Monad.State.Strict
import Data.List
import Debug.Trace

data ProofState = PS { thname            :: Name,
                       holes             :: [Name], -- ^ holes still to be solved
                       usedns            :: [Name], -- ^ used names, don't use again
                       nextname          :: Int,    -- ^ name supply, for locally unique names
                       global_nextname   :: Int, -- ^ a mirror of the global name supply,
                                                 --   for generating things like type tags
                                                 --   in reflection
                       pterm             :: ProofTerm, -- ^ current proof term
                       ptype             :: Type,   -- ^ original goal
                       dontunify         :: [Name], -- ^ explicitly given by programmer, leave it
                       unified           :: (Name, [(Name, Term)]),
                       notunified        :: [(Name, Term)],
                       dotted            :: [(Name, [Name])], -- ^ dot pattern holes + environment
                                                              -- either hole or something in env must turn up in the 'notunified' list during elaboration
                       solved            :: Maybe (Name, Term),
                       problems          :: Fails,
                       injective         :: [Name],
                       deferred          :: [Name], -- ^ names we'll need to define
                       implementations   :: [Name], -- ^ implementation arguments (for interfaces)
                       autos             :: [(Name, ([FailContext], [Name]))], -- ^ unsolved 'auto' implicits with their holes
                       psnames           :: [Name], -- ^ Local names okay to use in proof search
                       previous          :: Maybe ProofState, -- ^ for undo
                       context           :: Context,
                       datatypes         :: Ctxt TypeInfo,
                       plog              :: String,
                       unifylog          :: Bool,
                       done              :: Bool,
                       recents           :: [Name],
                       while_elaborating :: [FailContext],
                       constraint_ns     :: String
                     }

data Tactic = Attack
            | Claim Name Raw
            | ClaimFn Name Name Raw
            | Reorder Name
            | Exact Raw
            | Fill Raw
            | MatchFill Raw
            | PrepFill Name [Name]
            | CompleteFill
            | Regret
            | Solve
            | StartUnify Name
            | EndUnify
            | UnifyAll
            | Compute
            | ComputeLet Name
            | Simplify
            | WHNF_Compute
            | WHNF_ComputeArgs
            | EvalIn Raw
            | CheckIn Raw
            | Intro (Maybe Name)
            | IntroTy Raw (Maybe Name)
            | Forall Name RigCount (Maybe ImplicitInfo) Raw
            | LetBind Name Raw Raw
            | ExpandLet Name Term
            | Rewrite Raw
            | Induction Raw
            | CaseTac Raw
            | Equiv Raw
            | PatVar Name
            | PatBind Name RigCount
            | Focus Name
            | Defer [Name] Name
            | DeferType Name Raw [Name]
            | Implementation Name
            | AutoArg Name
            | SetInjective Name
            | MoveLast Name
            | MatchProblems Bool
            | UnifyProblems
            | UnifyGoal Raw
            | UnifyTerms Raw Raw
            | ProofState
            | Undo
            | QED
    deriving Show

-- Some utilites on proof and tactic states

instance Show ProofState where
    show ps | [] <- holes ps
          = show (thname ps) ++ ": no more goals"
    show ps | (h : hs) <- holes ps
          = let tm = pterm ps
                nm = thname ps
                OK g = goal (Just h) tm
                wkenv = premises g in
                "Other goals: " ++ show hs ++ "\n" ++
                showPs wkenv (reverse wkenv) ++ "\n" ++
                "-------------------------------- (" ++ show nm ++
                ") -------\n  " ++
                show h ++ " : " ++ showG wkenv (goalType g) ++ "\n"
         where showPs env [] = ""
               showPs env ((n, _, Let t v):bs)
                   = "  " ++ show n ++ " : " ++
                     showEnv env ({- normalise ctxt env -} t) ++ "   =   " ++
                     showEnv env ({- normalise ctxt env -} v) ++
                     "\n" ++ showPs env bs
               showPs env ((n, _, b):bs)
                   = "  " ++ show n ++ " : " ++
                     showEnv env ({- normalise ctxt env -} (binderTy b)) ++
                     "\n" ++ showPs env bs
               showG ps (Guess t v) = showEnv ps ({- normalise ctxt ps -} t) ++
                                         " =?= " ++ showEnv ps v
               showG ps b = showEnv ps (binderTy b)

instance Pretty ProofState OutputAnnotation where
  pretty ps | [] <- holes ps =
    pretty (thname ps) <+> colon <+> text " no more goals."
  pretty ps | (h : hs) <- holes ps =
    let tm = pterm ps
        OK g = goal (Just h) tm
        nm = thname ps in
    let wkEnv = premises g in
      text "Other goals" <+> colon <+> pretty hs <+>
      prettyPs wkEnv (reverse wkEnv) <+>
      text "---------- " <+> text "Focussing on" <> colon <+> pretty nm <+> text " ----------" <+>
      pretty h <+> colon <+> prettyGoal wkEnv (goalType g)
    where
      prettyGoal ps (Guess t v) =
        prettyEnv ps t <+> text "=?=" <+> prettyEnv ps v
      prettyGoal ps b = prettyEnv ps $ binderTy b

      prettyPs env [] = empty
      prettyPs env ((n, _, Let t v):bs) =
        nest nestingSize (pretty n <+> colon <+>
        prettyEnv env t <+> text "=" <+> prettyEnv env v <+>
        nest nestingSize (prettyPs env bs))
      prettyPs env ((n, _, b):bs) =
        nest nestingSize (pretty n <+> colon <+> prettyEnv env (binderTy b) <+>
        nest nestingSize (prettyPs env bs))

holeName i = sMN i "hole"

qshow :: Fails -> String
qshow fs = show (map (\ (x, y, hs, env, _, _, t) -> (t, map fstEnv env, x, y, hs)) fs)

match_unify' :: Context -> Env ->
                (TT Name, Maybe Provenance) ->
                (TT Name, Maybe Provenance) ->
                StateT TState TC [(Name, TT Name)]
match_unify' ctxt env (topx, xfrom) (topy, yfrom) =
   do ps <- get
      let while = while_elaborating ps
      let dont = dontunify ps
      let inj = injective ps
      traceWhen (unifylog ps)
                ("Matching " ++ show (topx, topy) ++
                 " in " ++ show env ++
                 "\nHoles: " ++ show (holes ps)
                  ++ "\n"
                  ++ "\n" ++ show (getProofTerm (pterm ps)) ++ "\n\n"
                 ) $
       case match_unify ctxt env (topx, xfrom) (topy, yfrom) inj (holes ps) while of
            OK u -> traceWhen (unifylog ps)
                        ("Matched " ++ show u) $
                     do let (h, ns) = unified ps
                        put (ps { unified = (h, u ++ ns) })
                        return u
            Error e -> traceWhen (unifylog ps)
                         ("No match " ++ show e) $
                        do put (ps { problems = (topx, topy, True,
                                                 env, e, while, Match) :
                                                 problems ps })
                           return []
--       traceWhen (unifylog ps)
--             ("Matched " ++ show (topx, topy) ++ " without " ++ show dont ++
--              "\nSolved: " ++ show u
--              ++ "\nCurrent problems:\n" ++ qshow (problems ps)
-- --              ++ show (pterm ps)
--              ++ "\n----------") $

mergeSolutions :: Env -> [(Name, TT Name)] -> StateT TState TC [(Name, TT Name)]
mergeSolutions env ns = merge [] ns
  where
    merge acc [] = return (reverse acc)
    merge acc ((n, t) : ns)
          | Just t' <- lookup n ns
              = do ps <- get
                   let probs = problems ps
                   put (ps { problems = probs ++ [(t,t',True,env,
                                                    CantUnify True (t, Nothing) (t', Nothing) (Msg "") (errEnv env) 0,
                                                     [], Unify)] })
                   merge acc ns
          | otherwise = merge ((n, t): acc) ns

dropSwaps :: [(Name, TT Name)] -> [(Name, TT Name)]
dropSwaps [] = []
dropSwaps (p@(x, P _ y _) : xs) | solvedIn y x xs = dropSwaps xs
  where solvedIn _ _ [] = False
        solvedIn y x ((y', P _ x' _) : xs) | y == y' && x == x' = True
        solvedIn y x (_ : xs) = solvedIn y x xs
dropSwaps (p : xs) = p : dropSwaps xs

unify' :: Context -> Env ->
          (TT Name, Maybe Provenance) ->
          (TT Name, Maybe Provenance) ->
          StateT TState TC [(Name, TT Name)]
unify' ctxt env (topx, xfrom) (topy, yfrom) =
   do ps <- get
      let while = while_elaborating ps
      let dont = dontunify ps
      let inj = injective ps
      (u, fails) <- traceWhen (unifylog ps)
                        ("Trying " ++ show (topx, topy) ++
                         "\nNormalised " ++ show (normalise ctxt env topx,
                                                  normalise ctxt env topy) ++
                         " in\n" ++ show env ++
                         "\nHoles: " ++ show (holes ps)
                         ++ "\nInjective: " ++ show (injective ps)
                         ++ "\n") $
                     lift $ unify ctxt env (topx, xfrom) (topy, yfrom) inj (holes ps)
                                  (map fst (notunified ps)) while
      let notu = filter (\ (n, t) -> case t of
--                                         P _ _ _ -> False
                                        _ -> n `elem` dont) u
      traceWhen (unifylog ps)
            ("Unified " ++ show (topx, topy) ++ " without " ++ show dont ++
             "\nSolved: " ++ show u ++ "\nNew problems: " ++ qshow fails
             ++ "\nNot unified:\n" ++ show (notunified ps)
             ++ "\nCurrent problems:\n" ++ qshow (problems ps)
--              ++ show (pterm ps)
             ++ "\n----------") $
        do let (h, ns) = unified ps
           -- solve in results (maybe unify should do this itself...)
           let u' = map (\(n, sol) -> (n, updateSolvedTerm u sol)) u
           -- if a metavar has multiple solutions, make a new unification
           -- problem for each.
           uns <- mergeSolutions env (u' ++ ns)
           ps <- get
           let (ns_p, probs') = updateProblems ps uns (fails ++ problems ps)
           let ns' = dropSwaps ns_p
           let (notu', probs_notu) = mergeNotunified env (holes ps) (notu ++ notunified ps)
           traceWhen (unifylog ps)
            ("Now solved: " ++ show ns' ++
             "\nNow problems: " ++ qshow (probs' ++ probs_notu) ++
             "\nNow injective: " ++ show (updateInj u (injective ps))) $
             put (ps { problems = probs' ++ probs_notu,
                       unified = (h, ns'),
                       injective = updateInj u (injective ps),
                       notunified = notu' })
           return u
  where updateInj ((n, a) : us) inj
              | (P _ n' _, _) <- unApply a,
                n `elem` inj = updateInj us (n':inj)
              | (P _ n' _, _) <- unApply a,
                n' `elem` inj = updateInj us (n:inj)
        updateInj (_ : us) inj = updateInj us inj
        updateInj [] inj = inj

nowElaboratingPS :: FC -> Name -> Name -> ProofState -> ProofState
nowElaboratingPS fc f arg ps = ps { while_elaborating = FailContext fc f arg : while_elaborating ps }

dropUntil :: (a -> Bool) -> [a] -> [a]
dropUntil p [] = []
dropUntil p (x:xs) | p x       = xs
                   | otherwise = dropUntil p xs

doneElaboratingAppPS :: Name -> ProofState -> ProofState
doneElaboratingAppPS f ps = let while = while_elaborating ps
                                while' = dropUntil (\ (FailContext _ f' _) -> f == f') while
                            in ps { while_elaborating = while' }

doneElaboratingArgPS :: Name -> Name -> ProofState -> ProofState
doneElaboratingArgPS f x ps = let while = while_elaborating ps
                                  while' = dropUntil (\ (FailContext _ f' x') -> f == f' && x == x') while
                              in ps { while_elaborating = while' }

getName :: Monad m => String -> StateT TState m Name
getName tag = do ps <- get
                 let n = nextname ps
                 put (ps { nextname = n+1 })
                 return $ sMN n tag

action :: Monad m => (ProofState -> ProofState) -> StateT TState m ()
action a = do ps <- get
              put (a ps)

query :: Monad m => (ProofState -> r) -> StateT TState m r
query q = do ps <- get
             return $ q ps

addLog :: Monad m => String -> StateT TState m ()
addLog str = action (\ps -> ps { plog = plog ps ++ str ++ "\n" })

newProof :: Name -- ^ the name of what's to be elaborated
         -> String -- ^ current source file
         -> Context -- ^ the current global context
         -> Ctxt TypeInfo -- ^ the value of the idris_datatypes field of IState
         -> Int -- ^ the value of the idris_name field of IState
         -> Type -- ^ the goal type
         -> ProofState
newProof n tcns ctxt datatypes globalNames ty =
  let h = holeName 0
      ty' = vToP ty
  in PS n [h] [] 1 globalNames (mkProofTerm (Bind h (Hole ty')
        (P Bound h ty'))) ty [] (h, []) [] []
        Nothing [] []
        [] [] [] []
        Nothing ctxt datatypes "" False False [] [] tcns

type TState = ProofState -- [TacticAction])
type RunTactic = RunTactic' TState

envAtFocus :: ProofState -> TC Env
envAtFocus ps
    | not $ null (holes ps) = do g <- goal (Just (head (holes ps))) (pterm ps)
                                 return (premises g)
    | otherwise = fail $ "No holes in " ++ show (getProofTerm (pterm ps))

goalAtFocus :: ProofState -> TC (Binder Type)
goalAtFocus ps
    | not $ null (holes ps) = do g <- goal (Just (head (holes ps))) (pterm ps)
                                 return (goalType g)
    | otherwise = Error . Msg $ "No goal in " ++ show (holes ps) ++ show (getProofTerm (pterm ps))

tactic :: Hole -> RunTactic -> StateT TState TC ()
tactic h f = do ps <- get
                (tm', _) <- atHole h f (context ps) [] (pterm ps)
                ps <- get -- might have changed while processing
                put (ps { pterm = tm' })

computeLet :: Context -> Name -> Term -> Term
computeLet ctxt n tm = cl [] tm where
   cl env (Bind n' (Let t v) sc)
       | n' == n = let v' = normalise ctxt env v in
                       Bind n' (Let t v') sc
   cl env (Bind n' b sc) = Bind n' (fmap (cl env) b) (cl ((n, Rig0, b):env) sc)
   cl env (App s f a) = App s (cl env f) (cl env a)
   cl env t = t

attack :: RunTactic
attack ctxt env (Bind x (Hole t) sc)
    = do h <- getName "hole"
         action (\ps -> ps { holes = h : holes ps })
         return $ Bind x (Guess t (newtm h)) sc
  where
    newtm h = Bind h (Hole t) (P Bound h t)
attack ctxt env _ = fail "Not an attackable hole"

claim :: Name -> Raw -> RunTactic
claim n ty ctxt env t =
    do (tyv, tyt) <- lift $ check ctxt env ty
       lift $ isType ctxt env tyt
       action (\ps -> let (g:gs) = holes ps in
                          ps { holes = g : n : gs } )
       return $ Bind n (Hole tyv) t

-- If the current goal is 'retty', make a claim which is a function that
-- can compute a retty from argty (i.e a claim 'argty -> retty')
claimFn :: Name -> Name -> Raw -> RunTactic
claimFn n bn argty ctxt env t@(Bind x (Hole retty) sc) =
    do (tyv, tyt) <- lift $ check ctxt env argty
       lift $ isType ctxt env tyt
       action (\ps -> let (g:gs) = holes ps in
                          ps { holes = g : n : gs } )
       return $ Bind n (Hole (Bind bn (Pi RigW Nothing tyv tyt) retty)) t
claimFn _ _ _ ctxt env _ = fail "Can't make function type here"

reorder_claims :: RunTactic
reorder_claims ctxt env t
    = -- trace (showSep "\n" (map show (scvs t))) $
      let (bs, sc) = scvs t []
          newbs = reverse (sortB (reverse bs)) in
          traceWhen (bs /= newbs) (show bs ++ "\n ==> \n" ++ show newbs) $
            return (bindAll newbs sc)
  where scvs (Bind n b@(Hole _) sc) acc = scvs sc ((n, b):acc)
        scvs sc acc = (reverse acc, sc)

        sortB :: [(Name, Binder (TT Name))] -> [(Name, Binder (TT Name))]
        sortB [] = []
        sortB (x:xs) | all (noOcc x) xs = x : sortB xs
                     | otherwise = sortB (insertB x xs)

        insertB x [] = [x]
        insertB x (y:ys) | all (noOcc x) (y:ys) = x : y : ys
                         | otherwise = y : insertB x ys

        noOcc (n, _) (_, Let t v) = noOccurrence n t && noOccurrence n v
        noOcc (n, _) (_, Guess t v) = noOccurrence n t && noOccurrence n v
        noOcc (n, _) (_, b) = noOccurrence n (binderTy b)

focus :: Name -> RunTactic
focus n ctxt env t = do action (\ps -> let hs = holes ps in
                                            if n `elem` hs
                                               then ps { holes = n : (hs \\ [n]) }
                                               else ps)
                        ps <- get
                        return t

movelast :: Name -> RunTactic
movelast n ctxt env t = do action (\ps -> let hs = holes ps in
                                              if n `elem` hs
                                                  then ps { holes = (hs \\ [n]) ++ [n] }
                                                  else ps)
                           return t

implementationArg :: Name -> RunTactic
implementationArg n ctxt env (Bind x (Hole t) sc)
    = do action (\ps -> let hs = holes ps
                            is = implementations ps in
                            ps { holes = (hs \\ [x]) ++ [x],
                                 implementations = x:is })
         return (Bind x (Hole t) sc)
implementationArg n ctxt env _
    = fail "The current focus is not a hole."

autoArg :: Name -> RunTactic
autoArg n ctxt env (Bind x (Hole t) sc)
    = do action (\ps -> case lookup x (autos ps) of
                             Nothing ->
                               let hs = holes ps in
                               ps { holes = (hs \\ [x]) ++ [x],
                                    autos = (x, (while_elaborating ps, refsIn t)) : autos ps }
                             Just _ -> ps)
         return (Bind x (Hole t) sc)
autoArg n ctxt env _
    = fail "The current focus not a hole."

setinj :: Name -> RunTactic
setinj n ctxt env (Bind x b sc)
    = do action (\ps -> let is = injective ps in
                            ps { injective = n : is })
         return (Bind x b sc)

defer :: [Name] -> Name -> RunTactic
defer dropped n ctxt env (Bind x (Hole t) (P nt x' ty)) | x == x' =
    do let env' = filter (\(n, _, t) -> n `notElem` dropped) env
       action (\ps -> let hs = holes ps in
                          ps { usedns = n : usedns ps,
                               holes = hs \\ [x] })
       ps <- get
       return (Bind n (GHole (length env') (psnames ps) (mkTy (reverse env') t))
                      (mkApp (P Ref n ty) (map getP (reverse env'))))
  where
    mkTy []           t = t
    mkTy ((n,rig,b) : bs) t = Bind n (Pi RigW Nothing (binderTy b) (TType (UVar [] 0))) (mkTy bs t)

    getP (n, rig, b) = P Bound n (binderTy b)
defer dropped n ctxt env _ = fail "Can't defer a non-hole focus."

-- as defer, but build the type and application explicitly
deferType :: Name -> Raw -> [Name] -> RunTactic
deferType n fty_in args ctxt env (Bind x (Hole t) (P nt x' ty)) | x == x' =
    do (fty, _) <- lift $ check ctxt env fty_in
       action (\ps -> let hs = holes ps
                          ds = deferred ps in
                          ps { holes = hs \\ [x],
                               deferred = n : ds })
       return (Bind n (GHole 0 [] fty)
                      (mkApp (P Ref n ty) (map getP args)))
  where
    getP n = case lookupBinder n env of
                  Just b -> P Bound n (binderTy b)
                  Nothing -> error ("deferType can't find " ++ show n)
deferType _ _ _ _ _ _ = fail "Can't defer a non-hole focus."

regret :: RunTactic
regret ctxt env (Bind x (Hole t) sc) | noOccurrence x sc =
    do action (\ps -> let hs = holes ps in
                          ps { holes = hs \\ [x] })
       return sc
regret ctxt env (Bind x (Hole t) _)
    = fail $ show x ++ " : " ++ show t ++ " is not solved..."
regret _ _ _ = fail "The current focus is not a hole."

unifyGoal :: Raw -> RunTactic
unifyGoal tm ctxt env h@(Bind x b sc) =
    do (tmv, _) <- lift $ check ctxt env tm
       ns' <- unify' ctxt env (binderTy b, Nothing) (tmv, Nothing)
       return h
unifyGoal _ _ _ _ = fail "The focus is not a binder."

unifyTerms :: Raw -> Raw -> RunTactic
unifyTerms tm1 tm2 ctxt env h =
    do (tm1v, _) <- lift $ check ctxt env tm1
       (tm2v, _) <- lift $ check ctxt env tm2
       ns' <- unify' ctxt env (tm1v, Nothing) (tm2v, Nothing)
       return h

exact :: Raw -> RunTactic
exact guess ctxt env (Bind x (Hole ty) sc) =
    do (val, valty) <- lift $ check ctxt env guess
       lift $ converts ctxt env valty ty
       return $ Bind x (Guess ty val) sc
exact _ _ _ _ = fail "Can't fill here."

-- As exact, but attempts to solve other goals by unification

fill :: Raw -> RunTactic
fill guess ctxt env (Bind x (Hole ty) sc) =
    do (val, valty) <- lift $ check ctxt env guess
--        let valtyn = normalise ctxt env valty
--        let tyn = normalise ctxt env ty
       ns <- unify' ctxt env (valty, Just $ SourceTerm val)
                             (ty, Just (chkPurpose val ty))
       ps <- get
       let (uh, uns) = unified ps
--        put (ps { unified = (uh, uns ++ ns) })
--        addLog (show (uh, uns ++ ns))
       return $ Bind x (Guess ty val) sc
  where
    -- some expected types show up commonly in errors and indicate a
    -- specific problem.
    --   argTy -> retTy suggests a function applied to too many arguments
    chkPurpose val (Bind _ (Pi _ _ (P _ (MN _ _) _) _) (P _ (MN _ _) _))
                   = TooManyArgs val
    chkPurpose _ _ = ExpectedType
fill _ _ _ _ = fail "Can't fill here."

-- As fill, but attempts to solve other goals by matching

match_fill :: Raw -> RunTactic
match_fill guess ctxt env (Bind x (Hole ty) sc) =
    do (val, valty) <- lift $ check ctxt env guess
--        let valtyn = normalise ctxt env valty
--        let tyn = normalise ctxt env ty
       ns <- match_unify' ctxt env (valty, Just $ SourceTerm val)
                                   (ty, Just ExpectedType)
       ps <- get
       let (uh, uns) = unified ps
--        put (ps { unified = (uh, uns ++ ns) })
--        addLog (show (uh, uns ++ ns))
       return $ Bind x (Guess ty val) sc
match_fill _ _ _ _ = fail "Can't fill here."

prep_fill :: Name -> [Name] -> RunTactic
prep_fill f as ctxt env (Bind x (Hole ty) sc) =
    do let val = mkApp (P Ref f Erased) (map (\n -> P Ref n Erased) as)
       return $ Bind x (Guess ty val) sc
prep_fill f as ctxt env t = fail $ "Can't prepare fill at " ++ show t

complete_fill :: RunTactic
complete_fill ctxt env (Bind x (Guess ty val) sc) =
    do let guess = forget val
       (val', valty) <- lift $ check ctxt env guess
       ns <- unify' ctxt env (valty, Just $ SourceTerm val')
                             (ty, Just ExpectedType)
       ps <- get
       let (uh, uns) = unified ps
--        put (ps { unified = (uh, uns ++ ns) })
       return $ Bind x (Guess ty val) sc
complete_fill ctxt env t = fail $ "Can't complete fill at " ++ show t

-- When solving something in the 'dont unify' set, we should check
-- that the guess we are solving it with unifies with the thing unification
-- found for it, if anything.

solve :: RunTactic
solve ctxt env (Bind x (Guess ty val) sc)
   = do ps <- get
        let (uh, uns) = unified ps
        dropdots <-
             case lookup x (notunified ps) of
                Just tm -> -- trace ("NEED MATCH: " ++ show (x, tm, val) ++ "\nIN " ++ show (pterm ps)) $
                            do match_unify' ctxt env (tm, Just InferredVal)
                                                     (val, Just GivenVal)
                               return [x]
                _ -> return []
        action (\ps -> ps { holes = traceWhen (unifylog ps) ("Dropping hole " ++ show x) $
                                       holes ps \\ [x],
                            solved = Just (x, val),
                            dontunify = filter (/= x) (dontunify ps),
                            notunified = updateNotunified [(x,val)]
                                           (notunified ps),
                            recents = x : recents ps,
                            implementations = implementations ps \\ [x],
                            dotted = dropUnified dropdots (dotted ps) })
        let (locked, did) = tryLock (holes ps \\ [x]) (updsubst x val sc) in
            return locked
  where dropUnified ddots [] = []
        dropUnified ddots ((x, es) : ds)
             | x `elem` ddots || any (\e -> e `elem` ddots) es
                  = dropUnified ddots ds
             | otherwise = (x, es) : dropUnified ddots ds

        tryLock :: [Name] -> Term -> (Term, Bool)
        tryLock hs tm@(App Complete _ _) = (tm, True)
        tryLock hs tm@(App s f a) =
             let (f', fl) = tryLock hs f
                 (a', al) = tryLock hs a in
                 if fl && al then (App Complete f' a', True)
                             else (App s f' a', False)
        tryLock hs t@(P _ n _) = (t, not $ n `elem` hs)
        tryLock hs t@(Bind n (Hole _) sc) = (t, False)
        tryLock hs t@(Bind n (Guess _ _) sc) = (t, False)
        tryLock hs t@(Bind n (Let ty val) sc)
            = let (ty', tyl) = tryLock hs ty
                  (val', vall) = tryLock hs val
                  (sc', scl) = tryLock hs sc in
                  (Bind n (Let ty' val') sc', tyl && vall && scl)
        tryLock hs t@(Bind n b sc)
            = let (bt', btl) = tryLock hs (binderTy b)
                  (val', vall) = tryLock hs val
                  (sc', scl) = tryLock hs sc in
                  (Bind n (b { binderTy = bt' }) sc', btl && scl)
        tryLock hs t = (t, True)

solve _ _ h@(Bind x t sc)
   = do ps <- get
        case findType x sc of
             Just t -> lift $ tfail (CantInferType (show t))
             _ -> lift $ tfail (IncompleteTerm h)
   where findType x (Bind n (Let t v) sc)
              = findType x v `mplus` findType x sc
         findType x (Bind n t sc)
              | P _ x' _ <- binderTy t, x == x' = Just n
              | otherwise = findType x sc
         findType x _ = Nothing

introTy :: Raw -> Maybe Name -> RunTactic
introTy ty mn ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do let n = case mn of
                  Just name -> name
                  Nothing -> x
       let t' = case t of
                    x@(Bind y (Pi _ _ s _) _) -> x
                    _ -> normalise ctxt env t
       (tyv, tyt) <- lift $ check ctxt env ty
--        ns <- lift $ unify ctxt env tyv t'
       case t' of
           Bind y (Pi rig _ s _) t -> let t' = updsubst y (P Bound n s) t in
                                        do ns <- unify' ctxt env (s, Nothing) (tyv, Nothing)
                                           ps <- get
                                           let (uh, uns) = unified ps
--                                            put (ps { unified = (uh, uns ++ ns) })
                                           return $ Bind n (Lam rig tyv) (Bind x (Hole t') (P Bound x t'))
           _ -> lift $ tfail $ CantIntroduce t'
introTy ty n ctxt env _ = fail "Can't introduce here."

intro :: Maybe Name -> RunTactic
intro mn ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do let t' = case t of
                    x@(Bind y (Pi _ _ s _) _) -> x
                    _ -> normalise ctxt env t
       case t' of
           Bind y (Pi rig _ s _) t ->
               let n = case mn of
                      Just name -> name
                      Nothing -> y
               -- It's important that this be subst and not updsubst,
               -- because we want to substitute even in portions of
               -- terms that we know do not contain holes.
                   t' = subst y (P Bound n s) t
               in return $ Bind n (Lam rig s) (Bind x (Hole t') (P Bound x t'))
           _ -> lift $ tfail $ CantIntroduce t'
intro n ctxt env _ = fail "Can't introduce here."

forall :: Name -> RigCount -> Maybe ImplicitInfo -> Raw -> RunTactic
forall n rig impl ty ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do (tyv, tyt) <- lift $ check ctxt env ty
       unify' ctxt env (tyt, Nothing) (TType (UVar [] 0), Nothing)
       unify' ctxt env (t, Nothing) (TType (UVar [] 0), Nothing)
       return $ Bind n (Pi rig impl tyv (TType (UVar [] 0))) (Bind x (Hole t) (P Bound x t))
forall n rig impl ty ctxt env _ = fail "Can't pi bind here"

patvar :: Name -> RunTactic
patvar n ctxt env (Bind x (Hole t) sc) =
    do action (\ps -> ps { holes = traceWhen (unifylog ps) ("Dropping pattern hole " ++ show x) $
                                     holes ps \\ [x],
                           solved = Just (x, P Bound n t),
                           dontunify = filter (/=x) (dontunify ps),
                           notunified = updateNotunified [(x,P Bound n t)]
                                          (notunified ps),
                           injective = addInj n x (injective ps)
                         })
       return $ Bind n (PVar RigW t) (updsubst x (P Bound n t) sc)
  where addInj n x ps | x `elem` ps = n : ps
                      | otherwise = ps
patvar n ctxt env tm = fail $ "Can't add pattern var at " ++ show tm

letbind :: Name -> Raw -> Raw -> RunTactic
letbind n ty val ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do (tyv,  tyt)  <- lift $ check ctxt env ty
       (valv, valt) <- lift $ check ctxt env val
       lift $ isType ctxt env tyt
       return $ Bind n (Let tyv valv) (Bind x (Hole t) (P Bound x t))
letbind n ty val ctxt env _ = fail "Can't let bind here"

expandLet :: Name -> Term -> RunTactic
expandLet n v ctxt env tm =
       return $ updsubst n v tm

rewrite :: Raw -> RunTactic
rewrite tm ctxt env (Bind x (Hole t) xp@(P _ x' _)) | x == x' =
    do (tmv, tmt) <- lift $ check ctxt env tm
       let tmt' = normalise ctxt env tmt
       case unApply tmt' of
         (P _ (UN q) _, [lt,rt,l,r]) | q == txt "=" ->
            do let p = Bind rname (Lam RigW lt) (mkP (P Bound rname lt) r l t)
               let newt = mkP l r l t
               let sc = forget $ (Bind x (Hole newt)
                                       (mkApp (P Ref (sUN "replace") (TType (UVal 0)))
                                              [lt, l, r, p, tmv, xp]))
               (scv, sct) <- lift $ check ctxt env sc
               return scv
         _ -> lift $ tfail (NotEquality tmv tmt')
  where rname = sMN 0 "replaced"
rewrite _ _ _ _ = fail "Can't rewrite here"

-- To make the P for rewrite, replace syntactic occurrences of l in ty with
-- an x, and put \x : lt in front
mkP :: TT Name -> TT Name -> TT Name -> TT Name -> TT Name
mkP lt l r ty | l == ty = lt
mkP lt l r (App s f a) = let f' = if (r /= f) then mkP lt l r f else f
                             a' = if (r /= a) then mkP lt l r a else a in
                             App s f' a'
mkP lt l r (Bind n b sc)
                     = let b' = mkPB b
                           sc' = if (r /= sc) then mkP lt l r sc else sc in
                           Bind n b' sc'
    where mkPB (Let t v) = let t' = if (r /= t) then mkP lt l r t else t
                               v' = if (r /= v) then mkP lt l r v else v in
                               Let t' v'
          mkPB b = let ty = binderTy b
                       ty' = if (r /= ty) then mkP lt l r ty else ty in
                             b { binderTy = ty' }
mkP lt l r x = x

casetac :: Raw -> Bool -> RunTactic
casetac tm induction ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' = do
  (tmv, tmt) <- lift $ check ctxt env tm
  let tmt' = normalise ctxt env tmt
  let (tacn, tacstr, tactt) = if induction
              then (ElimN, "eliminator", "Induction")
              else (CaseN (FC' emptyFC), "case analysis", "Case analysis")
  case unApply tmt' of
    (P _ tnm _, tyargs) -> do
        case lookupTy (SN (tacn tnm)) ctxt of
          [elimTy] -> do
             param_pos <- case lookupMetaInformation tnm ctxt of
                               [DataMI param_pos]    -> return param_pos
                               m | not (null tyargs) -> fail $ "Invalid meta information for " ++ show tnm ++ " where the metainformation is " ++ show m ++ " and definition is" ++ show (lookupDef tnm ctxt)
                               _ -> return []
             let (params, indicies) = splitTyArgs param_pos tyargs
             let args     = getArgTys elimTy
             let pmargs   = take (length params) args
             let args'    = drop (length params) args
             let propTy   = head args'
             let restargs = init $ tail args'
             let consargs = take (length restargs - length indicies) restargs
             let indxargs = drop (length restargs - length indicies) restargs
             let scr      = last $ tail args'
             let indxnames = makeIndexNames indicies
             currentNames <- query $ allTTNames . getProofTerm . pterm
             let tmnm = case tm of
                         Var nm -> uniqueNameCtxt ctxt nm currentNames
                         _ -> uniqueNameCtxt ctxt (sMN 0 "iv") currentNames
             let tmvar = P Bound tmnm tmt'
             prop <- replaceIndicies indxnames indicies $ Bind tmnm (Lam RigW tmt') (mkP tmvar tmv tmvar t)
             consargs' <- query (\ps -> map (flip (uniqueNameCtxt (context ps)) (holes ps ++ allTTNames (getProofTerm (pterm ps))) *** uniqueBindersCtxt (context ps) (holes ps ++ allTTNames (getProofTerm (pterm ps)))) consargs)
             let res = flip (foldr substV) params $ (substV prop $ bindConsArgs consargs' (mkApp (P Ref (SN (tacn tnm)) (TType (UVal 0)))
                                                        (params ++ [prop] ++ map makeConsArg consargs' ++ indicies ++ [tmv])))
             action (\ps -> ps {holes = holes ps \\ [x],
                                recents = x : recents ps })
             mapM_ addConsHole (reverse consargs')
             let res' = forget res
             (scv, sct) <- lift $ check ctxt env res'
             let (scv', _) = specialise ctxt env [] scv
             return scv'
          [] -> lift $ tfail $ NoEliminator tacstr tmt'
          xs -> lift $ tfail $ Msg $ "Multiple definitions found when searching for " ++ tacstr ++ "of " ++ show tnm
    _ -> lift $ tfail $ NoEliminator (if induction then "induction" else "case analysis")
                                     tmt'
    where scname = sMN 0 "scarg"
          makeConsArg (nm, ty) = P Bound nm ty
          bindConsArgs ((nm, ty):args) v = Bind nm (Hole ty) $ bindConsArgs args v
          bindConsArgs [] v = v
          addConsHole (nm, ty) =
            action (\ps -> ps { holes = nm : holes ps })
          splitTyArgs param_pos tyargs =
            let (params, indicies) = partition (flip elem param_pos . fst) . zip [0..] $ tyargs
            in (map snd params, map snd indicies)
          makeIndexNames = foldr (\_ nms -> (uniqueNameCtxt ctxt (sMN 0 "idx") nms):nms) []
          replaceIndicies idnms idxs prop = foldM (\t (idnm, idx) -> do (idxv, idxt) <- lift $ check ctxt env (forget idx)
                                                                        let var = P Bound idnm idxt
                                                                        return $ Bind idnm (Lam RigW idxt) (mkP var idxv var t)) prop $ zip idnms idxs
casetac tm induction ctxt env _ = fail $ "Can't do " ++ (if induction then "induction" else "case analysis") ++ " here"


equiv :: Raw -> RunTactic
equiv tm ctxt env (Bind x (Hole t) sc) =
    do (tmv, tmt) <- lift $ check ctxt env tm
       lift $ converts ctxt env tmv t
       return $ Bind x (Hole tmv) sc
equiv tm ctxt env _ = fail "Can't equiv here"

patbind :: Name -> RigCount -> RunTactic
patbind n rig ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do let t' = case t of
                    x@(Bind y (PVTy s) t) -> x
                    _ -> normalise ctxt env t
       case t' of
           Bind y (PVTy s) t -> let t' = updsubst y (P Bound n s) t in
                                    return $ Bind n (PVar rig s) (Bind x (Hole t') (P Bound x t'))
           _ -> fail "Nothing to pattern bind"
patbind n _ ctxt env _ = fail "Can't pattern bind here"

compute :: RunTactic
compute ctxt env (Bind x (Hole ty) sc) =
    do return $ Bind x (Hole (normalise ctxt env ty)) sc
compute ctxt env t = return t

whnf_compute :: RunTactic
whnf_compute ctxt env (Bind x (Hole ty) sc) =
    do let ty' = whnf ctxt env ty in
           return $ Bind x (Hole ty') sc
whnf_compute ctxt env t = return t

whnf_compute_args :: RunTactic
whnf_compute_args ctxt env (Bind x (Hole ty) sc) =
    do let ty' = whnfArgs ctxt env ty in
           return $ Bind x (Hole ty') sc
whnf_compute_args ctxt env t = return t

-- reduce let bindings only
simplify :: RunTactic
simplify ctxt env (Bind x (Hole ty) sc) =
    do return $ Bind x (Hole (fst (specialise ctxt env [] ty))) sc
simplify ctxt env t = return t

check_in :: Raw -> RunTactic
check_in t ctxt env tm =
    do (val, valty) <- lift $ check ctxt env t
       addLog (showEnv env val ++ " : " ++ showEnv env valty)
       return tm

eval_in :: Raw -> RunTactic
eval_in t ctxt env tm =
    do (val, valty) <- lift $ check ctxt env t
       let val' = normalise ctxt env val
       let valty' = normalise ctxt env valty
       addLog (showEnv env val ++ " : " ++
               showEnv env valty ++
--                     " in " ++ show env ++
               " ==>\n " ++
               showEnv env val' ++ " : " ++
               showEnv env valty')
       return tm

start_unify :: Name -> RunTactic
start_unify n ctxt env tm = do -- action (\ps -> ps { unified = (n, []) })
                               return tm

tmap f (a, b, c) = (f a, b, c)

solve_unified :: RunTactic
solve_unified ctxt env tm =
    do ps <- get
       let (_, ns) = unified ps
       let unify = dropGiven (dontunify ps) ns (holes ps)
       action (\ps -> ps { holes = traceWhen (unifylog ps) ("Dropping holes " ++ show (map fst unify)) $
                                     holes ps \\ map fst unify,
                           recents = recents ps ++ map fst unify })
       action (\ps -> ps { pterm = updateSolved unify (pterm ps) })
       return (updateSolvedTerm unify tm)

dropGiven du [] hs = []
dropGiven du ((n, P Bound t ty) : us) hs
   | n `elem` du && not (t `elem` du)
     && n `elem` hs && t `elem` hs
            = (t, P Bound n ty) : dropGiven du us hs
dropGiven du (u@(n, _) : us) hs
   | n `elem` du = dropGiven du us hs
-- dropGiven du (u@(_, P a n ty) : us) | n `elem` du = dropGiven du us
dropGiven du (u : us) hs = u : dropGiven du us hs

keepGiven du [] hs = []
keepGiven du ((n, P Bound t ty) : us) hs
   | n `elem` du && not (t `elem` du)
     && n `elem` hs && t `elem` hs
            = keepGiven du us hs
keepGiven du (u@(n, _) : us) hs
   | n `elem` du = u : keepGiven du us hs
keepGiven du (u : us) hs = keepGiven du us hs

updateEnv [] e = e
updateEnv ns [] = []
updateEnv ns ((n, rig, b) : env)
   = (n, rig, fmap (updateSolvedTerm ns) b) : updateEnv ns env

updateProv ns (SourceTerm t) = SourceTerm $ updateSolvedTerm ns t
updateProv ns p = p

updateError [] err = err
updateError ns (At f e) = At f (updateError ns e)
updateError ns (Elaborating s n ty e) = Elaborating s n ty (updateError ns e)
updateError ns (ElaboratingArg f a env e)
 = ElaboratingArg f a env (updateError ns e)
updateError ns (CantUnify b (l,lp) (r,rp) e xs sc)
 = CantUnify b (updateSolvedTerm ns l, fmap (updateProv ns) lp)
               (updateSolvedTerm ns r, fmap (updateProv ns) rp) (updateError ns e) xs sc
updateError ns e = e

updateRes ns [] = []
updateRes ns ((x, t) : ts) = (x, updateSolvedTerm ns t) : updateRes ns ts

solveInProblems x val [] = []
solveInProblems x val ((l, r, env, err) : ps)
   = ((psubst x val l, psubst x val r,
       updateEnv [(x, val)] env, err) : solveInProblems x val ps)

mergeNotunified :: Env -> [Name] -> [(Name, Term)] -> ([(Name, Term)], Fails)
mergeNotunified env holes ns = mnu ns [] [] where
  mnu [] ns_acc ps_acc = (reverse ns_acc, reverse ps_acc)
  mnu ((n, t):ns) ns_acc ps_acc
      | Just t' <- lookup n ns, t /= t'
             = mnu ns ((n,t') : ns_acc)
                      ((t,t',True, env,CantUnify True (t, Nothing) (t', Nothing) (Msg "") [] 0, [],Match) : ps_acc)
      | otherwise = mnu ns ((n,t) : ns_acc) ps_acc

updateNotunified [] nu = nu
updateNotunified ns nu = up nu where
  up [] = []
  up ((n, t) : nus) = let t' = updateSolvedTerm ns t in
                          ((n, t') : up nus)

getProvenance :: Err -> (Maybe Provenance, Maybe Provenance)
getProvenance (CantUnify _ (_, lp) (_, rp) _ _ _) = (lp, rp)
getProvenance _ = (Nothing, Nothing)

setReady (x, y, _, env, err, c, at) = (x, y, True, env, err, c, at)

updateProblems :: ProofState -> [(Name, TT Name)] -> Fails
                    -> ([(Name, TT Name)], Fails)
-- updateProblems ctxt [] ps inj holes = ([], ps)
updateProblems ps updates probs = rec 10 updates probs
 where
  -- keep trying if we make progress, but not too many times...
  rec 0 us fs = (us, fs)
  rec n us fs = case up us [] fs of
                     res@(_, []) -> res
                     res@(us', _) | length us' == length us -> res
                     (us', fs') -> rec (n - 1) us' fs'

  hs = holes ps
  inj = injective ps
  ctxt = context ps
  ulog = unifylog ps
  usupp = map fst (notunified ps)
  dont = dontunify ps

  up ns acc [] = (ns, map (updateNs ns) (reverse acc))
  up ns acc (prob@(x, y, ready, env, err, while, um) : ps) =
    let (x', newx) = updateSolvedTerm' ns x
        (y', newy) = updateSolvedTerm' ns y
        (lp, rp) = getProvenance err
        err' = updateError ns err
        env' = updateEnv ns env in
          if newx || newy || ready ||
             any (\n -> n `elem` inj) (refsIn x ++ refsIn y) then
            case unify ctxt env' (x', lp) (y', rp) inj hs usupp while of
                 OK (v, []) -> traceWhen ulog ("DID " ++ show (x',y',ready,v,dont)) $
                                let v' = filter (\(n, _) -> n `notElem` dont) v in
                                    up (ns ++ v') acc ps
                 e -> -- trace ("FAILED " ++ show (x',y',ready,e)) $
                      up ns ((x',y',False,env',err',while,um) : acc) ps
            else -- trace ("SKIPPING " ++ show (x,y,ready)) $
                 up ns ((x',y', False, env',err', while, um) : acc) ps

  updateNs ns (x, y, t, env, err, fc, fa)
       = let (x', newx) = updateSolvedTerm' ns x
             (y', newy) = updateSolvedTerm' ns y in
             (x', y', newx || newy,
                  updateEnv ns env, updateError ns err, fc, fa)

orderUpdateSolved :: [(Name, Term)] -> ProofTerm -> (ProofTerm, [Name])
orderUpdateSolved ns tm = update [] ns tm
  where
    update done [] t = (t, done)
    update done ((n, P _ n' _) : ns) t | n == n' = update done ns t
    update done (n : ns) t = update (fst n : done)
                                    (map (updateMatch n) ns)
                                    (updateSolved [n] t)

    -- Update the later solutions too
    updateMatch n (x, tm) = (x, updateSolvedTerm [n] tm)

-- attempt to solve remaining problems with match_unify
matchProblems :: Bool -> ProofState -> [(Name, TT Name)] -> Fails
                    -> ([(Name, TT Name)], Fails)
matchProblems all ps updates probs = up updates probs where
  hs = holes ps
  inj = injective ps
  ctxt = context ps

  up ns [] = (ns, [])
  up ns ((x, y, ready, env, err, while, um) : ps)
       | all || um == Match =
    let x' = updateSolvedTerm ns x
        y' = updateSolvedTerm ns y
        (lp, rp) = getProvenance err
        err' = updateError ns err
        env' = updateEnv ns env in
        case match_unify ctxt env' (x', lp) (y', rp) inj hs while of
            OK v -> -- trace ("Added " ++ show v ++ " from " ++ show (x', y')) $
                               up (ns ++ v) ps
            _ -> let (ns', ps') = up ns ps in
                     (ns', (x', y', True, env', err', while, um) : ps')
  up ns (p : ps) = let (ns', ps') = up ns ps in
                       (ns', p : ps')

processTactic :: Tactic -> ProofState -> TC (ProofState, String)
processTactic QED ps = case holes ps of
                           [] -> do let tm = {- normalise (context ps) [] -} getProofTerm (pterm ps)
                                    (tm', ty', _) <- recheck (constraint_ns ps) (context ps) [] (forget tm) tm
                                    return (ps { done = True, pterm = mkProofTerm tm' },
                                            "Proof complete: " ++ showEnv [] tm')
                           _  -> fail "Still holes to fill."
processTactic ProofState ps = return (ps, showEnv [] (getProofTerm (pterm ps)))
processTactic Undo ps = case previous ps of
                            Nothing -> Error . Msg $ "Nothing to undo."
                            Just pold -> return (pold, "")
processTactic EndUnify ps
    = let (h, ns_in) = unified ps
          ns = dropGiven (dontunify ps) ns_in (holes ps)
          ns' = map (\ (n, t) -> (n, updateSolvedTerm ns t)) ns
          (ns'', probs') = updateProblems ps ns' (problems ps)
          tm' = updateSolved ns'' (pterm ps) in
             traceWhen (unifylog ps) ("(EndUnify) Dropping holes: " ++ show (map fst ns'')) $
              return (ps { pterm = tm',
                           unified = (h, []),
                           problems = probs',
                           notunified = updateNotunified ns'' (notunified ps),
                           recents = recents ps ++ map fst ns'',
                           holes = holes ps \\ map fst ns'' }, "")
processTactic UnifyAll ps
    = let tm' = updateSolved (notunified ps) (pterm ps) in
          return (ps { pterm = tm',
                       notunified = [],
                       recents = recents ps ++ map fst (notunified ps),
                       holes = holes ps \\ map fst (notunified ps) }, "")
processTactic (Reorder n) ps
    = do ps' <- execStateT (tactic (Just n) reorder_claims) ps
         return (ps' { previous = Just ps, plog = "" }, plog ps')
processTactic (ComputeLet n) ps
    = return (ps { pterm = mkProofTerm $
                              computeLet (context ps) n
                                         (getProofTerm (pterm ps)) }, "")
processTactic UnifyProblems ps
    = do let (ns', probs') = updateProblems ps [] (map setReady (problems ps))
             (pterm', dropped) = orderUpdateSolved ns' (pterm ps)
         traceWhen (unifylog ps) ("(UnifyProblems) Dropping holes: " ++ show dropped) $
          return (ps { pterm = pterm', solved = Nothing, problems = probs',
                       previous = Just ps, plog = "",
                       notunified = updateNotunified ns' (notunified ps),
                       recents = recents ps ++ dropped,
                       dotted = filter (notIn ns') (dotted ps),
                       holes = holes ps \\ dropped }, plog ps)
   where notIn ns (h, _) = h `notElem` map fst ns
processTactic (MatchProblems all) ps
    = do let (ns', probs') = matchProblems all ps [] (map setReady (problems ps))
             (ns'', probs'') = matchProblems all ps ns' probs'
             (pterm', dropped) = orderUpdateSolved ns'' (resetProofTerm (pterm ps))
         traceWhen (unifylog ps) ("(MatchProblems) Dropping holes: " ++ show dropped) $
          return (ps { pterm = pterm', solved = Nothing, problems = probs'',
                       previous = Just ps, plog = "",
                       notunified = updateNotunified ns'' (notunified ps),
                       recents = recents ps ++ dropped,
                       holes = holes ps \\ dropped }, plog ps)
processTactic t ps
    = case holes ps of
        [] -> case t of
                   Focus _ -> return (ps, "") -- harmless to refocus when done, since
                                              -- 'focus' doesn't fail
                   _ -> fail $ "Proof done, nothing to run tactic on: " ++ show t ++
                              "\n" ++ show (getProofTerm (pterm ps))
        (h:_)  -> do ps' <- execStateT (process t h) ps
                     let (ns_in, probs')
                                = case solved ps' of
                                    Just s -> traceWhen (unifylog ps)
                                                ("SOLVED " ++ show s ++ " " ++ show (dontunify ps')) $
                                                updateProblems ps' [s] (problems ps')
                                    _ -> ([], problems ps')
                     -- rechecking problems may find more solutions, so
                     -- apply them here
                     let ns' = dropGiven (dontunify ps') ns_in (holes ps')
                     let pterm'' = updateSolved ns' (pterm ps')
                     traceWhen (unifylog ps)
                                 ("Updated problems after solve " ++ qshow probs' ++ "\n" ++
                                  "(Toplevel) Dropping holes: " ++ show (map fst ns') ++ "\n" ++
                                  "Holes were: " ++ show (holes ps')) $
                       return (ps' { pterm = pterm'',
                                     solved = Nothing,
                                     problems = probs',
                                     notunified = updateNotunified ns' (notunified ps'),
                                     previous = Just ps, plog = "",
                                     recents = recents ps' ++ map fst ns',
                                     holes = holes ps' \\ (map fst ns')
                                   }, plog ps')

process :: Tactic -> Name -> StateT TState TC ()
process EndUnify _
   = do ps <- get
        let (h, _) = unified ps
        tactic (Just h) solve_unified
process t h = tactic (Just h) (mktac t)
   where mktac Attack            = attack
         mktac (Claim n r)       = claim n r
         mktac (ClaimFn n bn r)  = claimFn n bn r
         mktac (Exact r)         = exact r
         mktac (Fill r)          = fill r
         mktac (MatchFill r)     = match_fill r
         mktac (PrepFill n ns)   = prep_fill n ns
         mktac CompleteFill      = complete_fill
         mktac Solve             = solve
         mktac (StartUnify n)    = start_unify n
         mktac Compute           = compute
         mktac Simplify          = Idris.Core.ProofState.simplify
         mktac WHNF_Compute      = whnf_compute
         mktac WHNF_ComputeArgs  = whnf_compute_args
         mktac (Intro n)         = intro n
         mktac (IntroTy ty n)    = introTy ty n
         mktac (Forall n r i t)  = forall n r i t
         mktac (LetBind n t v)   = letbind n t v
         mktac (ExpandLet n b)   = expandLet n b
         mktac (Rewrite t)       = rewrite t
         mktac (Induction t)     = casetac t True
         mktac (CaseTac t)       = casetac t False
         mktac (Equiv t)         = equiv t
         mktac (PatVar n)        = patvar n
         mktac (PatBind n rig)   = patbind n rig
         mktac (CheckIn r)       = check_in r
         mktac (EvalIn r)        = eval_in r
         mktac (Focus n)         = focus n
         mktac (Defer ns n)      = defer ns n
         mktac (DeferType n t a) = deferType n t a
         mktac (Implementation n)= implementationArg n
         mktac (AutoArg n)       = autoArg n
         mktac (SetInjective n)  = setinj n
         mktac (MoveLast n)      = movelast n
         mktac (UnifyGoal r)     = unifyGoal r
         mktac (UnifyTerms x y)  = unifyTerms x y

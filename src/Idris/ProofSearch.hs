{-# LANGUAGE PatternGuards #-}

module Idris.ProofSearch(trivial, trivialHoles, proofSearch, resolveTC) where

import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.TT
import Idris.Core.Unify
import Idris.Core.Evaluate
import Idris.Core.CaseTree
import Idris.Core.Typecheck

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Error

import Control.Applicative ((<$>))
import Control.Monad
import Control.Monad.State.Strict
import qualified Data.Set as S
import Data.List
import Debug.Trace

-- Pass in a term elaborator to avoid a cyclic dependency with ElabTerm

trivial :: (PTerm -> ElabD ()) -> IState -> ElabD ()
trivial = trivialHoles [] []

trivialHoles :: [Name] -> -- user visible names, when working
                          -- in interactive mode
                [(Name, Int)] -> (PTerm -> ElabD ()) -> IState -> ElabD ()
trivialHoles psnames ok elab ist
     = try' (do elab (PApp (fileFC "prf") (PRef (fileFC "prf") [] eqCon) [pimp (sUN "A") Placeholder False, pimp (sUN "x") Placeholder False])
                return ())
            (do env <- get_env
                g <- goal
                tryAll env
                return ()) True
      where
        tryAll []     = fail "No trivial solution"
        tryAll ((x, b):xs)
           = do -- if type of x has any holes in it, move on
                hs <- get_holes
                let badhs = hs -- filter (flip notElem holesOK) hs
                g <- goal
                -- anywhere but the top is okay for a hole, if holesOK set
                if -- all (\n -> not (n `elem` badhs)) (freeNames (binderTy b))
                   (holesOK hs (binderTy b) && (null psnames || x `elem` psnames))
                   then try' (elab (PRef (fileFC "prf") [] x))
                             (tryAll xs) True
                   else tryAll xs
        
        holesOK hs ap@(App _ _ _)
           | (P _ n _, args) <- unApply ap
                = holeArgsOK hs n 0 args
        holesOK hs (App _ f a) = holesOK hs f && holesOK hs a
        holesOK hs (P _ n _) = not (n `elem` hs)
        holesOK hs (Bind n b sc) = holesOK hs (binderTy b) && 
                                   holesOK hs sc
        holesOK hs _ = True

        holeArgsOK hs n p [] = True
        holeArgsOK hs n p (a : as)
           | (n, p) `elem` ok = holeArgsOK hs n (p + 1) as
           | otherwise = holesOK hs a && holeArgsOK hs n (p + 1) as

trivialTCs :: [(Name, Int)] -> (PTerm -> ElabD ()) -> IState -> ElabD ()
trivialTCs ok elab ist
     = try' (do elab (PApp (fileFC "prf") (PRef (fileFC "prf") [] eqCon) [pimp (sUN "A") Placeholder False, pimp (sUN "x") Placeholder False])
                return ())
            (do env <- get_env
                g <- goal
                tryAll env
                return ()) True
      where
        tryAll []     = fail "No trivial solution"
        tryAll ((x, b):xs)
           = do -- if type of x has any holes in it, move on
                hs <- get_holes
                let badhs = hs -- filter (flip notElem holesOK) hs
                g <- goal
                env <- get_env
                -- anywhere but the top is okay for a hole, if holesOK set
                if -- all (\n -> not (n `elem` badhs)) (freeNames (binderTy b))
                   (holesOK hs (binderTy b) && tcArg env (binderTy b))
                   then try' (elab (PRef (fileFC "prf") [] x))
                             (tryAll xs) True
                   else tryAll xs
       
        tcArg env ty 
           | (P _ n _, args) <- unApply (getRetTy (normalise (tt_ctxt ist) env ty))
                 = case lookupCtxtExact n (idris_classes ist) of
                        Just _ -> True
                        _ -> False
           | otherwise = False

        holesOK hs ap@(App _ _ _)
           | (P _ n _, args) <- unApply ap
                = holeArgsOK hs n 0 args
        holesOK hs (App _ f a) = holesOK hs f && holesOK hs a
        holesOK hs (P _ n _) = not (n `elem` hs)
        holesOK hs (Bind n b sc) = holesOK hs (binderTy b) && 
                                   holesOK hs sc
        holesOK hs _ = True

        holeArgsOK hs n p [] = True
        holeArgsOK hs n p (a : as)
           | (n, p) `elem` ok = holeArgsOK hs n (p + 1) as
           | otherwise = holesOK hs a && holeArgsOK hs n (p + 1) as

cantSolveGoal :: ElabD a
cantSolveGoal = do g <- goal
                   env <- get_env
                   lift $ tfail $
                      CantSolveGoal g (map (\(n,b) -> (n, binderTy b)) env) 

proofSearch :: Bool -> -- recursive search (False for 'refine') 
               Bool -> -- invoked from a tactic proof. If so, making
                       -- new metavariables is meaningless, and there shoudl
                       -- be an error reported instead.
               Bool -> -- ambiguity ok
               Bool -> -- defer on failure
               Int -> -- maximum depth
               (PTerm -> ElabD ()) -> Maybe Name -> Name -> 
               [Name] ->
               [Name] ->
               IState -> ElabD ()
proofSearch False fromProver ambigok deferonfail depth elab _ nroot psnames [fn] ist
       = do -- get all possible versions of the name, take the first one that
            -- works
            let all_imps = lookupCtxtName fn (idris_implicits ist)
            tryAllFns all_imps
  where
    -- if nothing worked, make a new metavariable
    tryAllFns [] | fromProver = cantSolveGoal  
    tryAllFns [] = do attack; defer [] nroot; solve
    tryAllFns (f : fs) = try' (tryFn f) (tryAllFns fs) True

    tryFn (f, args) = do let imps = map isImp args
                         ps <- get_probs
                         hs <- get_holes
                         args <- map snd <$> try' (apply (Var f) imps)
                                                  (match_apply (Var f) imps) True
                         ps' <- get_probs
--                          when (length ps < length ps') $ fail "Can't apply constructor"
                         -- Make metavariables for new holes 
                         hs' <- get_holes
                         ptm <- get_term
                         if fromProver then cantSolveGoal
                           else do
                             mapM_ (\ h -> do focus h
                                              attack; defer [] nroot; solve) 
                                 (hs' \\ hs)
--                                  (filter (\ (x, y) -> not x) (zip (map fst imps) args))
                             solve

    isImp (PImp p _ _ _ _) = (True, p)
    isImp arg = (True, priority arg) -- try to get all of them by unification
proofSearch rec fromProver ambigok deferonfail maxDepth elab fn nroot psnames hints ist 
       = do compute
            ty <- goal
            hs <- get_holes
            env <- get_env
            tm <- get_term
            argsok <- conArgsOK ty
            if ambigok || argsok then
               case lookupCtxt nroot (idris_tyinfodata ist) of
                    [TISolution ts] -> findInferredTy ts
                    _ -> psRec rec maxDepth [] S.empty
               else do ptm <- get_term
                       autoArg (sUN "auto") -- not enough info in the type yet
  where
    findInferredTy (t : _) = elab (delab ist (toUN t)) 

    conArgsOK ty
       = let (f, as) = unApply ty in
           case f of
              P _ n _ -> 
                let autohints = case lookupCtxtExact n (idris_autohints ist) of
                                     Nothing -> []
                                     Just hs -> hs in
                    case lookupCtxtExact n (idris_datatypes ist) of
                              Just t -> do rs <- mapM (conReady as) 
                                                      (autohints ++ con_names t)
                                           return (and rs)
                              Nothing -> -- local variable, go for it
                                    return True
              TType _ -> return True
              _ -> fail "Not a data type"

    conReady :: [Term] -> Name -> ElabD Bool
    conReady as n 
       = case lookupTyExact n (tt_ctxt ist) of
              Just ty -> do let (_, cs) = unApply (getRetTy ty)
                            -- if any metavariables in 'as' correspond to
                            -- a constructor form in 'cs', then we're not
                            -- ready to run auto yet. Otherwise, go for it
                            hs <- get_holes
                            return $ and (map (notHole hs) (zip as cs))
              Nothing -> fail "Can't happen"

    -- if n is a metavariable, and c is a constructor form, we're not ready
    -- to run yet
    notHole hs (P _ n _, c)
       | (P _ cn _, _) <- unApply c,
         n `elem` hs && isConName cn (tt_ctxt ist) = False
       | Constant _ <- c = not (n `elem` hs)
    -- if fa is a metavariable applied to anything, we're not ready to run yet.
    notHole hs (fa, c)
       | (P _ fn _, args@(_:_)) <- unApply fa = fn `notElem` hs
    notHole _ _ = True

    inHS hs (P _ n _) = n `elem` hs
    isHS _ _ = False

    toUN t@(P nt (MN i n) ty) 
       | ('_':xs) <- str n = t
       | otherwise = P nt (UN n) ty
    toUN (App s f a) = App s (toUN f) (toUN a)
    toUN t = t

    -- psRec counts depth and the local variable applications we're under
    -- (so we don't try a pointless application of something to itself,
    -- which obviously won't work anyway but might lead us on a wild
    -- goose chase...)
    -- Also keep track of the types we've proved so far in this branch
    -- (if we get back to one we've been to before, we're just in a cycle and
    -- that's no use)
    psRec :: Bool -> Int -> [Name] -> S.Set Type -> ElabD ()
    psRec _ 0 locs tys | fromProver = cantSolveGoal
    psRec rec 0 locs tys = do attack; defer [] nroot; solve --fail "Maximum depth reached"
    psRec False d locs tys = tryCons d locs tys hints 
    psRec True d locs tys
                 = do compute
                      ty <- goal
                      when (S.member ty tys) $ fail "Been here before"
                      let tys' = S.insert ty tys
                      try' (try' (trivialHoles psnames [] elab ist)
                                 (resolveTC False False 20 ty nroot elab ist)
                                 True)
                           (try' (try' (resolveByCon (d - 1) locs tys') 
                                       (resolveByLocals (d - 1) locs tys')
                                 True)
             -- if all else fails, make a new metavariable
                         (if fromProver 
                             then fail "cantSolveGoal"
                             else do attack; defer [] nroot; solve) True) True

    -- get recursive function name. Only user given names make sense.
    getFn d (Just f) | d < maxDepth-1 && usersname f = [f]
                     | otherwise = []
    getFn d _ = []

    usersname (UN _) = True
    usersname (NS n _) = usersname n
    usersname _ = False

    resolveByCon d locs tys
        = do t <- goal
             let (f, _) = unApply t
             case f of
                P _ n _ -> 
                   do let autohints = case lookupCtxtExact n (idris_autohints ist) of
                                           Nothing -> []
                                           Just hs -> hs
                      case lookupCtxtExact n (idris_datatypes ist) of
                          Just t -> do
                             let others = hints ++ con_names t ++ autohints
                             when (not fromProver && length (con_names t) > 1)
                                   -- in interactive mode,
                                   -- don't just guess (fine for 'auto',
                                   -- since that's part of the point...)
                                   $ checkConstructor ist others
                             tryCons d locs tys (others ++ getFn d fn)
                          Nothing -> fail "Not a data type"
                _ -> fail "Not a data type"

    -- if there are local variables which have a function type, try
    -- applying them too
    resolveByLocals d locs tys
        = do env <- get_env
             tryLocals d locs tys env

    tryLocals d locs tys [] = fail "Locals failed"
    tryLocals d locs tys ((x, t) : xs) 
       | x `elem` locs || x `notElem` psnames = tryLocals d locs tys xs
       | otherwise = try' (tryLocal d (x : locs) tys x t) 
                          (tryLocals d locs tys xs) True

    tryCons d locs tys [] = fail "Constructors failed"
    tryCons d locs tys (c : cs) 
        = try' (tryCon d locs tys c) (tryCons d locs tys cs) True

    tryLocal d locs tys n t 
          = do let a = getPArity (delab ist (binderTy t))
               tryLocalArg d locs tys n a

    tryLocalArg d locs tys n 0 = elab (PRef (fileFC "prf") [] n)
    tryLocalArg d locs tys n i 
        = simple_app False (tryLocalArg d locs tys n (i - 1))
                (psRec True d locs tys) "proof search local apply"

    -- Like type class resolution, but searching with constructors
    tryCon d locs tys n = 
         do ty <- goal
            let imps = case lookupCtxtExact n (idris_implicits ist) of
                            Nothing -> []
                            Just args -> map isImp args
            ps <- get_probs
            hs <- get_holes
            args <- map snd <$> try' (apply (Var n) imps)
                                     (match_apply (Var n) imps) True
            ps' <- get_probs
            hs' <- get_holes
            when (length ps < length ps') $ fail "Can't apply constructor"
            let newhs = filter (\ (x, y) -> not x) (zip (map fst imps) args)
            mapM_ (\ (_, h) -> do focus h
                                  aty <- goal
                                  psRec True d locs tys) newhs      
            solve

    isImp (PImp p _ _ _ _) = (True, p)
    isImp arg = (False, priority arg) 

-- In interactive mode, only search for things if there is some 
-- index to help pick a relevant constructor
checkConstructor :: IState -> [Name] -> ElabD ()
checkConstructor ist [] = return ()
checkConstructor ist (n : ns) =
    case lookupTyExact n (tt_ctxt ist) of
         Just t -> if not (conIndexed t)
                      then fail "Overlapping constructor types"
                      else checkConstructor ist ns
  where
    conIndexed t = let (_, args) = unApply (getRetTy t) in
                       any conHead args
    conHead t | (P _ n _, _) <- unApply t = case lookupDefExact n (tt_ctxt ist) of
                                                 Just _ -> True
                                                 _ -> False
              | otherwise = False

-- | Resolve type classes. This will only pick up 'normal' instances, never
-- named instances (which is enforced by 'findInstances').
resolveTC :: Bool -- ^ using default Int
          -> Bool -- ^ allow metavariables in the goal
          -> Int -- ^ depth
          -> Term -- ^ top level goal, for error messages
          -> Name -- ^ top level function name, to prevent loops
          -> (PTerm -> ElabD ()) -- ^ top level elaborator
          -> IState -> ElabD ()
resolveTC def mvok depth top fn elab ist
   = do hs <- get_holes
        resTC' [] def hs depth top fn elab ist

resTC' tcs def topholes 0 topg fn elab ist = fail $ "Can't resolve type class"
resTC' tcs def topholes 1 topg fn elab ist = try' (trivial elab ist) (resolveTC def False 0 topg fn elab ist) True
resTC' tcs defaultOn topholes depth topg fn elab ist
  = do compute
       g <- goal
       -- Resolution can proceed only if there is something concrete in the
       -- determining argument positions. Keep track of the holes in the
       -- non-determining position, because it's okay for 'trivial' to solve
       -- those holes and no others.
       let (argsok, okholePos) = case tcArgsOK g topholes of
                                    Nothing -> (False, [])
                                    Just hs -> (True, hs)
       if not argsok -- && not mvok)
         then lift $ tfail $ CantResolve True topg
         else do
           ptm <- get_term
           ulog <- getUnifyLog
           hs <- get_holes
           env <- get_env
           t <- goal
           let (tc, ttypes) = unApply (getRetTy t)
           let okholes = case tc of
                              P _ n _ -> zip (repeat n) okholePos
                              _ -> []

           traceWhen ulog ("Resolving class " ++ show g ++ "\nin" ++ show env ++ "\n" ++ show okholes) $
            try' (trivialTCs okholes elab ist) 
                (do addDefault t tc ttypes
                    let stk = map fst (filter snd $ elab_stack ist)
                    let insts = findInstances ist t
                    blunderbuss t depth stk (stk ++ insts)) True
  where
    -- returns Just hs if okay, where hs are holes which are okay in the
    -- goal, or Nothing if not okay to proceed
    tcArgsOK ty hs | (P _ nc _, as) <- unApply (getRetTy ty), nc == numclass && defaultOn
       = Just []
    tcArgsOK ty hs -- if any determining arguments are metavariables, postpone
       = let (f, as) = unApply (getRetTy ty) in
             case f of
                  P _ cn _ -> case lookupCtxtExact cn (idris_classes ist) of
                                   Just ci -> tcDetArgsOK 0 (class_determiners ci) hs as
                                   Nothing -> if any (isMeta hs) as
                                                 then Nothing
                                                 else Just []
                  _ -> if any (isMeta hs) as
                          then Nothing
                          else Just []

    -- return the list of argument positions which can safely be a hole
    -- or Nothing if one of the determining arguments is a hole
    tcDetArgsOK i ds hs (x : xs)
        | i `elem` ds = if isMeta hs x
                           then Nothing
                           else tcDetArgsOK (i + 1) ds hs xs
        | otherwise = do rs <- tcDetArgsOK (i + 1) ds hs xs
                         case x of
                              P _ n _ -> Just (i : rs)
                              _ -> Just rs
    tcDetArgsOK _ _ _ [] = Just []

    isMeta :: [Name] -> Term -> Bool
    isMeta ns (P _ n _) = n `elem` ns 
    isMeta _ _ = False

    notHole hs (P _ n _, c)
       | (P _ cn _, _) <- unApply (getRetTy c),
         n `elem` hs && isConName cn (tt_ctxt ist) = False
       | Constant _ <- c = not (n `elem` hs)
    notHole _ _ = True

    -- HACK! Rather than giving a special name, better to have some kind
    -- of flag in ClassInfo structure
    chaser (UN nm)
        | ('@':'@':_) <- str nm = True -- old way
    chaser (SN (ParentN _ _)) = True
    chaser (NS n _) = chaser n
    chaser _ = False

    numclass = sNS (sUN "Num") ["Classes","Prelude"]

    addDefault t num@(P _ nc _) [P Bound a _] | nc == numclass && defaultOn
        = do focus a
             fill (RConstant (AType (ATInt ITBig))) -- default Integer
             solve
    addDefault t f as
          | all boundVar as = return () -- True -- fail $ "Can't resolve " ++ show t
    addDefault t f a = return () -- trace (show t) $ return ()

    boundVar (P Bound _ _) = True
    boundVar _ = False

    blunderbuss t d stk [] = do -- c <- get_env
                            -- ps <- get_probs
                            lift $ tfail $ CantResolve False topg
    blunderbuss t d stk (n:ns)
        | n /= fn -- && (n `elem` stk)
              = tryCatch (resolve n d)
                    (\e -> case e of
                             CantResolve True _ -> lift $ tfail e
                             _ -> blunderbuss t d stk ns)
        | otherwise = blunderbuss t d stk ns

    introImps = do g <- goal
                   case g of
                        (Bind _ (Pi _ _ _) sc) -> do attack; intro Nothing
                                                     num <- introImps
                                                     return (num + 1)
                        _ -> return 0

    solven 0 = return ()
    solven n = do solve; solven (n - 1)

    resolve n depth
       | depth == 0 = fail $ "Can't resolve type class"
       | otherwise
           = do lams <- introImps
                t <- goal
                let (tc, ttypes) = trace (show t) $ unApply (getRetTy t)
--                 if (all boundVar ttypes) then resolveTC (depth - 1) fn insts ist
--                   else do
                   -- if there's a hole in the goal, don't even try
                let imps = case lookupCtxtName n (idris_implicits ist) of
                                [] -> []
                                [args] -> map isImp (snd args) -- won't be overloaded!
                                xs -> error "The impossible happened - overloading is not expected here!"
                ps <- get_probs
                tm <- get_term
                args <- map snd <$> apply (Var n) imps
                solven lams -- close any implicit lambdas we introduced
                ps' <- get_probs
                when (length ps < length ps' || unrecoverable ps') $
                     fail "Can't apply type class"
--                 traceWhen (all boundVar ttypes) ("Progress: " ++ show t ++ " with " ++ show n) $
                mapM_ (\ (_,n) -> do focus n
                                     t' <- goal
                                     let (tc', ttype) = unApply (getRetTy t')
                                     let got = fst (unApply (getRetTy t))
                                     let depth' = if tc' `elem` tcs
                                                     then depth - 1 else depth
                                     resTC' (got : tcs) defaultOn topholes depth' topg fn elab ist)
                      (filter (\ (x, y) -> not x) (zip (map fst imps) args))
                -- if there's any arguments left, we've failed to resolve
                hs <- get_holes
                ulog <- getUnifyLog
                solve
                traceWhen ulog ("Got " ++ show n) $ return ()
       where isImp (PImp p _ _ _ _) = (True, p)
             isImp arg = (False, priority arg)

-- | Find the names of instances that have been designeated for
-- searching (i.e. non-named instances or instances from Elab scripts)
findInstances :: IState -> Term -> [Name]
findInstances ist t
    | (P _ n _, _) <- unApply (getRetTy t)
        = case lookupCtxt n (idris_classes ist) of
            [CI _ _ _ _ _ ins _] ->
              [n | (n, True) <- ins, accessible n]
            _ -> []
    | otherwise = []
  where accessible n = case lookupDefAccExact n False (tt_ctxt ist) of
                            Just (_, Hidden) -> False
                            _ -> True



module Idris.ElabTerm where

import Idris.AbsSyntax

import Core.Elaborate hiding (Tactic(..))
import Core.TT
import Core.Evaluate

import Control.Monad
import Control.Monad.State
import Data.List
import Debug.Trace

-- Data to pass to recursively called elaborators; e.g. for where blocks,
-- paramaterised declarations, etc.

data ElabInfo = EInfo { params :: [(Name, PTerm)],
                        inblock :: Ctxt [Name], -- names in the block, and their params
                        liftname :: Name -> Name,
                        namespace :: Maybe [String] }

toplevel = EInfo [] emptyContext id Nothing

-- Using the elaborator, convert a term in raw syntax to a fully
-- elaborated, typechecked term.
--
-- If building a pattern match, we convert undeclared variables from
-- holes to pattern bindings.

-- Also find deferred names in the term and their types

build :: IState -> ElabInfo -> Bool -> PTerm -> Elab (Term, [(Name, Type)])
build ist info pattern tm 
    = do elab ist info pattern tm
         tt <- get_term
         return $ runState (collectDeferred tt) []

elab :: IState -> ElabInfo -> Bool -> PTerm -> Elab ()
elab ist info pattern tm 
    = do elabE tm
         when pattern -- convert remaining holes to pattern vars
              mkPat
  where
    isph arg = case getTm arg of
        Placeholder -> True
        _ -> False

    toElab arg = case getTm arg of
        Placeholder -> Nothing
        v -> Just (priority arg, elabE v)

    mkPat = do hs <- get_holes
               case hs of
                  (h: hs) -> do patvar h; mkPat
                  [] -> return ()

    elabE t = {- do g <- goal
                 tm <- get_term
                 trace ("Elaborating " ++ show t ++ " : " ++ show g ++ "\n\tin " ++ show tm) 
                    $ -} elab' t

    local f = do e <- get_env
                 return (f `elem` map fst e)

    elab' PSet           = do fill RSet; solve
    elab' (PConstant c)  = do apply (RConstant c) []; solve
    elab' (PQuote r)     = do fill r; solve
    elab' (PTrue fc)     = try (elab' (PRef fc unitCon))
                               (elab' (PRef fc unitTy))
    elab' (PFalse fc)    = elab' (PRef fc falseTy)
    elab' (PResolveTC (FC "HACK" _)) -- for chasing parent classes
       = resolveTC 2 ist
    elab' (PResolveTC fc) = do c <- unique_hole (MN 0 "c")
                               instanceArg c
    elab' (PRefl fc)     = elab' (PApp fc (PRef fc eqCon) [pimp (MN 0 "a") Placeholder,
                                                           pimp (MN 0 "x") Placeholder])
    elab' (PEq fc l r)   = elab' (PApp fc (PRef fc eqTy) [pimp (MN 0 "a") Placeholder,
                                                          pimp (MN 0 "b") Placeholder,
                                                          pexp l, pexp r])
    elab' (PPair fc l r) = try (elabE (PApp fc (PRef fc pairTy)
                                            [pexp l,pexp r]))
                               (elabE (PApp fc (PRef fc pairCon)
                                            [pimp (MN 0 "A") Placeholder,
                                             pimp (MN 0 "B") Placeholder,
                                             pexp l, pexp r]))
    elab' (PDPair fc l@(PRef _ n) t r)
            = case t of 
                Placeholder -> try asType asValue
                _ -> asType
         where asType = elab' (PApp fc (PRef fc sigmaTy)
                                        [pexp t,
                                         pexp (PLam n Placeholder r)])
               asValue = elab' (PApp fc (PRef fc existsCon)
                                         [pimp (MN 0 "a") t,
                                          pimp (MN 0 "P") Placeholder,
                                          pexp l, pexp r])
    elab' (PDPair fc l t r) = elab' (PApp fc (PRef fc existsCon)
                                            [pimp (MN 0 "a") t,
                                             pimp (MN 0 "P") Placeholder,
                                             pexp l, pexp r])
    elab' (PAlternative as) 
        = let as' = pruneAlt as in
              try (tryAll (zip (map elab' as') (map showHd as')))
                  (tryAll (zip (map elab' as) (map showHd as)))
        where showHd (PApp _ h _) = show h
              showHd x = show x
    elab' (PRef fc n) | pattern && not (inparamBlock n)
                         = do ctxt <- get_context
                              let sc = case lookupTy Nothing n ctxt of
                                          [] -> True
                                          _ -> False
                              if sc
                                then erun fc $ 
                                       try (do apply (Var n) []; solve)
                                           (patvar n)
                                else do apply (Var n) []; solve 
      where inparamBlock n = case lookupCtxtName Nothing n (inblock info) of
                                [] -> False
                                _ -> True
    elab' (PRef fc n) = erun fc $ do apply (Var n) []; solve
    elab' (PLam n Placeholder sc)
          = do attack; intro (Just n); elabE sc; solve
    elab' (PLam n ty sc)
          = do tyn <- unique_hole (MN 0 "lamty")
               claim tyn RSet
               attack
               introTy (Var tyn) (Just n)
               -- end_unify
               focus tyn
               elabE ty
               elabE sc
               solve
    elab' (PPi _ n Placeholder sc)
          = do attack; arg n (MN 0 "ty"); elabE sc; solve
    elab' (PPi _ n ty sc) 
          = do attack; tyn <- unique_hole (MN 0 "ty")
               claim tyn RSet
               n' <- case n of 
                        MN _ _ -> unique_hole n
                        _ -> return n
               forall n' (Var tyn)
               focus tyn
               elabE ty
               elabE sc
               solve
    elab' (PLet n ty val sc)
          = do attack;
               tyn <- unique_hole (MN 0 "letty")
               claim tyn RSet
               valn <- unique_hole (MN 0 "letval")
               claim valn (Var tyn)
               letbind n (Var tyn) (Var valn)
               case ty of
                   Placeholder -> return ()
                   _ -> do focus tyn
                           elabE ty
               focus valn
               elabE val
               elabE sc
               solve
    elab' (PApp fc (PRef _ f) args')
       = do let args = {- case lookupCtxt f (inblock info) of
                          Just ps -> (map (pexp . (PRef fc)) ps ++ args')
                          _ ->-} args'
            ivs <- get_instances
            try (do ns <- apply (Var f) (map isph args)
                    solve
                    let (ns', eargs) 
                         = unzip $
                              sortBy (\(_,x) (_,y) -> compare (priority x) (priority y))
                                     (zip ns args)
                    elabArgs [] False ns' (map (\x -> (lazyarg x, getTm x)) eargs))
                (do apply_elab f (map toElab args)
                    solve)
            ivs' <- get_instances
            when (not pattern) $
                mapM_ (\n -> do focus n
                                resolveTC 7 ist) (ivs' \\ ivs) 
--             ivs <- get_instances
--             when (not (null ivs)) $
--               do t <- get_term
--                  trace (show ivs ++ "\n" ++ show t) $ 
--                    mapM_ (\n -> do focus n
--                                    resolveTC ist) ivs
      where tcArg (n, PConstraint _ _ Placeholder) = True
            tcArg _ = False

    elab' (PApp fc f [arg])
          = erun fc $ 
             do simple_app (elabE f) (elabE (getTm arg))
                solve
    elab' Placeholder = do (h : hs) <- get_holes
                           movelast h
    elab' (PMetavar n) = let n' = case namespace info of
                                    Just xs@(_:_) -> NS n xs
                                    _ -> n in
                             do attack; defer n'; solve
    elab' (PProof ts) = do mapM_ (runTac True ist) ts
    elab' (PTactics ts) = do mapM_ (runTac False ist) ts
    elab' (PElabError e) = fail e
    elab' x = fail $ "Not implemented " ++ show x

    elabArgs failed retry [] _
        | retry = let (ns, ts) = unzip (reverse failed) in
                      elabArgs [] False ns ts
        | otherwise = return ()
    elabArgs failed r (n:ns) ((_, Placeholder) : args) 
        = elabArgs failed r ns args
    elabArgs failed r (n:ns) ((lazy, t) : args)
        | lazy && not pattern 
          = do elabArg n (PApp bi (PRef bi (UN "lazy"))
                               [pimp (UN "a") Placeholder,
                                pexp t]); 
        | otherwise = elabArg n t
      where elabArg n t = if r
                            then try (do focus n; elabE t; elabArgs failed r ns args) 
                                     (elabArgs ((n,(lazy, t)):failed) r ns args)
                            else do focus n; elabE t; elabArgs failed r ns args
   
pruneAlt :: [PTerm] -> [PTerm]
pruneAlt xs = map prune xs
  where
    prune (PApp fc1 (PRef fc2 f) as) 
        = PApp fc1 (PRef fc2 f) (fmap (fmap (choose f)) as)
    prune t = t

    choose f (PAlternative as) = PAlternative (filter (headIs f) as)
    choose f t = t

    headIs f (PApp _ (PRef _ f') _) = f == f'
    headIs f _ = True -- keep if it's not an application

trivial :: IState -> Elab ()
trivial ist = try (elab ist toplevel False (PRefl (FC "prf" 0)))
                  (do env <- get_env
                      tryAll (map fst env))
      where
        tryAll []     = fail "No trivial solution"
        tryAll (x:xs) = try (elab ist toplevel False (PRef (FC "prf" 0) x))
                            (tryAll xs)

resolveTC :: Int -> IState -> Elab ()
resolveTC 0 ist = fail $ "Can't resolve type class"
resolveTC depth ist 
         = try (trivial ist)
               (do t <- goal
                   let (tc, ttypes) = unApply t
                   needsDefault t tc ttypes
                   tm <- get_term
--                    traceWhen (depth > 6) ("GOAL: " ++ show t ++ "\nTERM: " ++ show tm) $
--                        (tryAll (map elabTC (map fst (ctxtAlist (tt_ctxt ist)))))
                   blunderbuss t (map fst (ctxtAlist (tt_ctxt ist))))
  where
    elabTC n | tcname n = (resolve n depth, show n)
             | otherwise = (fail "Can't resolve", show n)

    needsDefault t num@(P _ (NS (UN "Num") ["builtins"]) _) [P Bound a _]
        = do focus a
             fill (RConstant IType) -- default Int
             solve
--     needsDefault t f as
--         | all boundVar as = fail $ "Can't resolve " ++ show t
    needsDefault t f a = return ()

    boundVar (P Bound _ _) = True
    boundVar _ = False

    blunderbuss t [] = fail $ "Can't resolve type class " ++ show t
    blunderbuss t (n:ns) | tcname n = try (resolve n depth)
                                          (blunderbuss t ns)
                         | otherwise = blunderbuss t ns
    tcname (UN ('@':_)) = True
    tcname (NS n _) = tcname n
    tcname _ = False

    resolve n depth
       | depth == 0 = fail $ "Can't resolve type class"
       | otherwise 
              = do t <- goal
                   let imps = case lookupCtxtName Nothing n (idris_implicits ist) of
                                [] -> []
                                [args] -> map isImp (snd args) -- won't be overloaded!
                   args <- apply (Var n) imps
                   mapM_ (\ (_,n) -> do focus n
                                        resolveTC (depth - 1) ist) 
                         (filter (\ (x, y) -> not x) (zip imps args))
                   solve
       where isImp (PImp _ _ _ _) = True
             isImp _ = False

collectDeferred :: Term -> State [(Name, Type)] Term
collectDeferred (Bind n (GHole t) app) =
    do ds <- get
       put ((n, t) : ds)
       return app
collectDeferred (Bind n b t) = do b' <- cdb b
                                  t' <- collectDeferred t
                                  return (Bind n b' t')
  where
    cdb (Let t v)   = liftM2 Let (collectDeferred t) (collectDeferred v)
    cdb (Guess t v) = liftM2 Guess (collectDeferred t) (collectDeferred v)
    cdb b           = do ty' <- collectDeferred (binderTy b)
                         return (b { binderTy = ty' })
collectDeferred (App f a) = liftM2 App (collectDeferred f) (collectDeferred a)
collectDeferred t = return t

-- Running tactics directly

runTac :: Bool -> IState -> PTactic -> Elab ()
runTac autoSolve ist tac = runT (fmap (addImpl ist) tac) where
    runT (Intro []) = do g <- goal
                         attack; intro (bname g)
      where
        bname (Bind n _ _) = Just n
        bname _ = Nothing
    runT (Intro xs) = mapM_ (\x -> do attack; intro (Just x)) xs
    runT (Exact tm) = do elab ist toplevel False tm
                         when autoSolve solveAll
    runT (Refine fn [])   
        = do (fn', imps) <- case lookupCtxtName Nothing fn (idris_implicits ist) of
                                    [] -> do a <- envArgs fn
                                             return (fn, a)
                                    -- FIXME: resolve ambiguities
                                    [(n, args)] -> return $ (n, map isImp args)
             ns <- apply (Var fn') imps
             when autoSolve solveAll
       where isImp (PImp _ _ _ _) = True
             isImp _ = False
             envArgs n = do e <- get_env
                            case lookup n e of
                               Just t -> return $ map (const False)
                                                      (getArgTys (binderTy t))
                               _ -> return []
    runT (Refine fn imps) = do ns <- apply (Var fn) imps
                               when autoSolve solveAll
    runT (Rewrite tm) -- to elaborate tm, let bind it, then rewrite by that
              = do attack; -- (h:_) <- get_holes
                   tyn <- unique_hole (MN 0 "rty")
                   -- start_unify h
                   claim tyn RSet
                   valn <- unique_hole (MN 0 "rval")
                   claim valn (Var tyn)
                   letn <- unique_hole (MN 0 "rewrite_rule")
                   letbind letn (Var tyn) (Var valn)  
                   focus valn
                   elab ist toplevel False tm
                   rewrite (Var letn)
                   when autoSolve solveAll
    runT (LetTac n tm)
              = do attack
                   tyn <- unique_hole (MN 0 "letty")
                   claim tyn RSet
                   valn <- unique_hole (MN 0 "letval")
                   claim valn (Var tyn)
                   letn <- unique_hole n
                   letbind letn (Var tyn) (Var valn)
                   focus valn
                   elab ist toplevel False tm
                   when autoSolve solveAll
    runT Compute = compute
    runT Trivial = do trivial ist; when autoSolve solveAll
    runT (Focus n) = focus n
    runT Solve = solve
    runT (Try l r) = do try (runT l) (runT r)
    runT (TSeq l r) = do runT l; runT r
    runT x = fail $ "Not implemented " ++ show x

solveAll = try (do solve; solveAll) (return ())

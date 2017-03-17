{-|
Module      : Idris.Elab.Term
Description : Code to elaborate terms.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE LambdaCase, PatternGuards, ViewPatterns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Idris.Elab.Term where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Core.CaseTree (SC, SC'(STerm), findCalls, findUsedArgs)
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.ProofTerm (getProofTerm)
import Idris.Core.TT
import Idris.Core.Typecheck (check, converts, isType, recheck)
import Idris.Core.Unify
import Idris.Core.WHNF (whnf, whnfArgs)
import Idris.Coverage (genClauses, recoverableCoverage, validCoverageCase)
import Idris.Delaborate
import Idris.DSL
import Idris.Elab.Quasiquote (extractUnquotes)
import Idris.Elab.Rewrite
import Idris.Elab.Utils
import Idris.Error
import Idris.ErrReverse (errReverse)
import Idris.Output (pshow)
import Idris.ProofSearch
import Idris.Reflection
import Idris.Termination (buildSCG, checkDeclTotality, checkPositive)

import qualified Util.Pretty as U

import Control.Applicative ((<$>))
import Control.Monad
import Control.Monad.State.Strict
import Data.Foldable (for_)
import Data.List
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromMaybe, mapMaybe, maybeToList)
import qualified Data.Set as S
import qualified Data.Text as T
import Debug.Trace

data ElabMode = ETyDecl | ETransLHS | ELHS | EImpossible | ERHS
  deriving Eq


data ElabResult = ElabResult {
    -- | The term resulting from elaboration
    resultTerm :: Term
    -- | Information about new metavariables
  , resultMetavars :: [(Name, (Int, Maybe Name, Type, [Name]))]
    -- | Deferred declarations as the meaning of case blocks
  , resultCaseDecls :: [PDecl]
    -- | The potentially extended context from new definitions
  , resultContext :: Context
    -- | Meta-info about the new type declarations
  , resultTyDecls :: [RDeclInstructions]
    -- | Saved highlights from elaboration
  , resultHighlighting :: [(FC, OutputAnnotation)]
    -- | The new global name counter
  , resultName :: Int
  }



-- | Using the elaborator, convert a term in raw syntax to a fully
-- elaborated, typechecked term.
--
-- If building a pattern match, we convert undeclared variables from
-- holes to pattern bindings.
--
-- Also find deferred names in the term and their types
build :: IState
      -> ElabInfo
      -> ElabMode
      -> FnOpts
      -> Name
      -> PTerm
      -> ElabD ElabResult
build ist info emode opts fn tm
    = do elab ist info emode opts fn tm
         let tmIn = tm
         let inf = case lookupCtxt fn (idris_tyinfodata ist) of
                        [TIPartial] -> True
                        _ -> False

         hs <- get_holes
         ivs <- get_implementations
         ptm <- get_term
         -- Resolve remaining interfaces. Two passes - first to get the
         -- default Num implementations, second to clean up the rest
         when (not pattern) $
              mapM_ (\n -> when (n `elem` hs) $
                             do focus n
                                g <- goal
                                try (resolveTC' True True 10 g fn ist)
                                    (movelast n)) ivs
         ivs <- get_implementations
         hs <- get_holes
         when (not pattern) $
              mapM_ (\n -> when (n `elem` hs) $
                             do focus n
                                g <- goal
                                ptm <- get_term
                                resolveTC' True True 10 g fn ist) ivs

         when (not pattern) $ solveAutos ist fn False

         tm <- get_term
         ctxt <- get_context
         probs <- get_probs
         u <- getUnifyLog
         hs <- get_holes

         when (not pattern) $
           traceWhen u ("Remaining holes:\n" ++ show hs ++ "\n" ++
                        "Remaining problems:\n" ++ qshow probs) $
             do unify_all; matchProblems True; unifyProblems

         when (not pattern) $ solveAutos ist fn True

         probs <- get_probs
         case probs of
            [] -> return ()
            ((_,_,_,_,e,_,_):es) -> traceWhen u ("Final problems:\n" ++ qshow probs ++ "\nin\n" ++ show tm) $
                                     if inf then return ()
                                            else lift (Error e)

         when tydecl (do mkPat
                         update_term liftPats
                         update_term orderPats)
         EState is _ impls highlights _ _ <- getAux
         tt <- get_term
         ctxt <- get_context
         let (tm, ds) = runState (collectDeferred (Just fn) (map fst is) ctxt tt) []
         log <- getLog
         g_nextname <- get_global_nextname
         if log /= ""
            then trace log $ return (ElabResult tm ds (map snd is) ctxt impls highlights g_nextname)
            else return (ElabResult tm ds (map snd is) ctxt impls highlights g_nextname)
  where pattern = emode == ELHS || emode == EImpossible
        tydecl = emode == ETyDecl

        mkPat = do hs <- get_holes
                   tm <- get_term
                   case hs of
                      (h: hs) -> do patvar h; mkPat
                      [] -> return ()

-- | Build a term autogenerated as an interface method definition.
--
-- (Separate, so we don't go overboard resolving things that we don't
-- know about yet on the LHS of a pattern def)

buildTC :: IState -> ElabInfo -> ElabMode -> FnOpts -> Name ->
         [Name] -> -- Cached names in the PTerm, before adding PAlternatives
         PTerm ->
         ElabD ElabResult
buildTC ist info emode opts fn ns tm
    = do let tmIn = tm
         let inf = case lookupCtxt fn (idris_tyinfodata ist) of
                        [TIPartial] -> True
                        _ -> False
         -- set name supply to begin after highest index in tm
         initNextNameFrom ns
         elab ist info emode opts fn tm
         probs <- get_probs
         tm <- get_term
         case probs of
            [] -> return ()
            ((_,_,_,_,e,_,_):es) -> if inf then return ()
                                           else lift (Error e)
         dots <- get_dotterm
         -- 'dots' are the PHidden things which have not been solved by
         -- unification
         when (not (null dots)) $
            lift (Error (CantMatch (getInferTerm tm)))
         EState is _ impls highlights _ _ <- getAux
         tt <- get_term
         ctxt <- get_context
         let (tm, ds) = runState (collectDeferred (Just fn) (map fst is) ctxt tt) []
         log <- getLog
         g_nextname <- get_global_nextname
         if (log /= "")
            then trace log $ return (ElabResult tm ds (map snd is) ctxt impls highlights g_nextname)
            else return (ElabResult tm ds (map snd is) ctxt impls highlights g_nextname)
  where pattern = emode == ELHS || emode == EImpossible

-- | return whether arguments of the given constructor name can be
-- matched on. If they're polymorphic, no, unless the type has beed
-- made concrete by the time we get around to elaborating the
-- argument.
getUnmatchable :: Context -> Name -> [Bool]
getUnmatchable ctxt n | isDConName n ctxt && n /= inferCon
   = case lookupTyExact n ctxt of
          Nothing -> []
          Just ty -> checkArgs [] [] ty
  where checkArgs :: [Name] -> [[Name]] -> Type -> [Bool]
        checkArgs env ns (Bind n (Pi _ _ t _) sc)
            = let env' = case t of
                              TType _ -> n : env
                              _ -> env in
                  checkArgs env' (intersect env (refsIn t) : ns)
                            (instantiate (P Bound n t) sc)
        checkArgs env ns t
            = map (not . null) (reverse ns)

getUnmatchable ctxt n = []

data ElabCtxt = ElabCtxt { e_inarg :: Bool,
                           e_isfn :: Bool, -- ^ Function part of application
                           e_guarded :: Bool,
                           e_intype :: Bool,
                           e_qq :: Bool,
                           e_nomatching :: Bool -- ^ can't pattern match
                         }

initElabCtxt = ElabCtxt False False False False False False

goal_polymorphic :: ElabD Bool
goal_polymorphic =
   do ty <- goal
      case ty of
           P _ n _ -> do env <- get_env
                         case lookupBinder n env of
                              Nothing -> return False
                              _ -> return True
           _ -> return False

-- | Returns the set of declarations we need to add to complete the
-- definition (most likely case blocks to elaborate) as well as
-- declarations resulting from user tactic scripts (%runElab)
elab :: IState
     -> ElabInfo
     -> ElabMode
     -> FnOpts
     -> Name
     -> PTerm
     -> ElabD ()
elab ist info emode opts fn tm
    = do let loglvl = opt_logLevel (idris_options ist)
         when (loglvl > 5) $ unifyLog True
         compute -- expand type synonyms, etc
         let fc = maybe "(unknown)"
         elabE initElabCtxt (elabFC info) tm -- (in argument, guarded, in type, in qquote)
         est <- getAux
         sequence_ (get_delayed_elab est)
         end_unify
         when (pattern || intransform) $
              -- convert remaining holes to pattern vars
              do unify_all
                 matchProblems False -- only the ones we matched earlier
                 unifyProblems
                 mkPat
                 update_term liftPats
         ptm <- get_term
         when pattern $
              -- Look for Rig1 (linear) pattern bindings
              do let pnms = findLinear ist [] ptm
                 update_term (setLinear pnms)
  where
    pattern = emode == ELHS || emode == EImpossible
    eimpossible = emode == EImpossible
    intransform = emode == ETransLHS
    bindfree = emode == ETyDecl || emode == ELHS || emode == ETransLHS
               || emode == EImpossible
    autoimpls = opt_autoimpls (idris_options ist)

    get_delayed_elab est =
        let ds = delayed_elab est in
            map snd $ sortBy (\(p1, _) (p2, _) -> compare p1 p2) ds

    tcgen = Dictionary `elem` opts
    reflection = Reflection `elem` opts

    isph arg = case getTm arg of
        Placeholder -> (True, priority arg)
        tm -> (False, priority arg)

    toElab ina arg = case getTm arg of
        Placeholder -> Nothing
        v -> Just (priority arg, elabE ina (elabFC info) v)

    toElab' ina arg = case getTm arg of
        Placeholder -> Nothing
        v -> Just (elabE ina (elabFC info) v)

    mkPat = do hs <- get_holes
               tm <- get_term
               case hs of
                  (h: hs) -> do patvar h; mkPat
                  [] -> return ()

    elabRec = elabE initElabCtxt Nothing

    -- | elabE elaborates an expression, possibly wrapping implicit coercions
    -- and forces/delays.  If you make a recursive call in elab', it is
    -- normally correct to call elabE - the ones that don't are `desugarings
    -- typically
    elabE :: ElabCtxt -> Maybe FC -> PTerm -> ElabD ()
    elabE ina fc' t =
     do solved <- get_recents
        as <- get_autos
        hs <- get_holes
        -- If any of the autos use variables which have recently been solved,
        -- have another go at solving them now.
        mapM_ (\(a, (failc, ns)) ->
                       if any (\n -> n `elem` solved) ns && head hs /= a
                              then solveAuto ist fn False (a, failc)
                              else return ()) as

        apt <- expandToArity t
        itm <- if not pattern then insertImpLam ina apt else return apt
        ct <- insertCoerce ina itm
        t' <- insertLazy ina ct
        g <- goal
        tm <- get_term
        ps <- get_probs
        hs <- get_holes

        --trace ("Elaborating " ++ show t' ++ " in " ++ show g
        --         ++ "\n" ++ show tm
        --         ++ "\nholes " ++ show hs
        --         ++ "\nproblems " ++ show ps
        --         ++ "\n-----------\n") $
        --trace ("ELAB " ++ show t') $
        env <- get_env
        let fc = fileFC "Force"
        handleError (forceErr t' env)
            (elab' ina fc' t')
            (elab' ina fc' (PApp fc (PRef fc [] (sUN "Force"))
                             [pimp (sUN "t") Placeholder True,
                              pimp (sUN "a") Placeholder True,
                              pexp ct]))

    forceErr orig env (CantUnify _ (t,_) (t',_) _ _ _)
       | (P _ (UN ht) _, _) <- unApply (normalise (tt_ctxt ist) env t),
            ht == txt "Delayed" = notDelay orig
    forceErr orig env (CantUnify _ (t,_) (t',_) _ _ _)
       | (P _ (UN ht) _, _) <- unApply (normalise (tt_ctxt ist) env t'),
            ht == txt "Delayed" = notDelay orig
    forceErr orig env (InfiniteUnify _ t _)
       | (P _ (UN ht) _, _) <- unApply (normalise (tt_ctxt ist) env t),
            ht == txt "Delayed" = notDelay orig
    forceErr orig env (Elaborating _ _ _ t) = forceErr orig env t
    forceErr orig env (ElaboratingArg _ _ _ t) = forceErr orig env t
    forceErr orig env (At _ t) = forceErr orig env t
    forceErr orig env t = False

    notDelay t@(PApp _ (PRef _ _ (UN l)) _) | l == txt "Delay" = False
    notDelay _ = True

    local f = do e <- get_env
                 return (f `elem` map fstEnv e)

    -- | Is a constant a type?
    constType :: Const -> Bool
    constType (AType _) = True
    constType StrType = True
    constType VoidType = True
    constType _ = False

    -- "guarded" means immediately under a constructor, to help find patvars

    elab' :: ElabCtxt  -- ^ (in an argument, guarded, in a type, in a quasiquote)
          -> Maybe FC -- ^ The closest FC in the syntax tree, if applicable
          -> PTerm -- ^ The term to elaborate
          -> ElabD ()
    elab' ina fc (PNoImplicits t) = elab' ina fc t -- skip elabE step
    elab' ina fc (PType fc')       =
      do apply RType []
         solve
         highlightSource fc' (AnnType "Type" "The type of types")
    elab' ina fc (PUniverse fc' u)   =
      do unless (UniquenessTypes `elem` idris_language_extensions ist
                  || e_qq ina) $
           lift $ tfail $ At fc' (Msg "You must turn on the UniquenessTypes extension to use UniqueType or AnyType")
         apply (RUType u) []
         solve
         highlightSource fc' (AnnType (show u) "The type of unique types")
--  elab' (_,_,inty) (PConstant c)
--     | constType c && pattern && not reflection && not inty
--       = lift $ tfail (Msg "Typecase is not allowed")
    elab' ina fc tm@(PConstant fc' c)
         | pattern && not reflection && not (e_qq ina) && not (e_intype ina)
           && isTypeConst c
              = lift $ tfail $ Msg ("No explicit types on left hand side: " ++ show tm)
         | pattern && not reflection && not (e_qq ina) && e_nomatching ina
              = lift $ tfail $ Msg ("Attempting concrete match on polymorphic argument: " ++ show tm)
         | otherwise = do apply (RConstant c) []
                          solve
                          highlightSource fc' (AnnConst c)
    elab' ina fc (PQuote r)     = do fill r; solve
    elab' ina _ (PTrue fc _)   =
       do compute
          g <- goal
          case g of
            TType _ -> elab' ina (Just fc) (PRef fc [] unitTy)
            UType _ -> elab' ina (Just fc) (PRef fc [] unitTy)
            _ -> elab' ina (Just fc) (PRef fc [] unitCon)
    elab' ina fc (PResolveTC (FC "HACK" _ _)) -- for chasing parent interfaces
       = do g <- goal; resolveTC False False 5 g fn elabRec ist
    elab' ina fc (PResolveTC fc')
        = do c <- getNameFrom (sMN 0 "__interface")
             implementationArg c
    -- Elaborate the equality type first homogeneously, then
    -- heterogeneously as a fallback
    elab' ina _ (PApp fc (PRef _ _ n) args)
       | n == eqTy, [Placeholder, Placeholder, l, r] <- map getTm args
       = try (do tyn <- getNameFrom (sMN 0 "aqty")
                 claim tyn RType
                 movelast tyn
                 elab' ina (Just fc) (PApp fc (PRef fc [] eqTy)
                              [pimp (sUN "A") (PRef NoFC [] tyn) True,
                               pimp (sUN "B") (PRef NoFC [] tyn) False,
                               pexp l, pexp r]))
             (do atyn <- getNameFrom (sMN 0 "aqty")
                 btyn <- getNameFrom (sMN 0 "bqty")
                 claim atyn RType
                 movelast atyn
                 claim btyn RType
                 movelast btyn
                 elab' ina (Just fc) (PApp fc (PRef fc [] eqTy)
                   [pimp (sUN "A") (PRef NoFC [] atyn) True,
                    pimp (sUN "B") (PRef NoFC [] btyn) False,
                    pexp l, pexp r]))

    elab' ina _ (PPair fc hls _ l r)
        = do compute
             g <- goal
             let (tc, _) = unApply g
             case g of
                TType _ -> elab' ina (Just fc) (PApp fc (PRef fc hls pairTy)
                                                      [pexp l,pexp r])
                UType _ -> elab' ina (Just fc) (PApp fc (PRef fc hls upairTy)
                                                      [pexp l,pexp r])
                _ -> case tc of
                        P _ n _ | n == upairTy
                          -> elab' ina (Just fc) (PApp fc (PRef fc hls upairCon)
                                                [pimp (sUN "A") Placeholder False,
                                                 pimp (sUN "B") Placeholder False,
                                                 pexp l, pexp r])
                        _ -> elab' ina (Just fc) (PApp fc (PRef fc hls pairCon)
                                                [pimp (sUN "A") Placeholder False,
                                                 pimp (sUN "B") Placeholder False,
                                                 pexp l, pexp r])
    elab' ina _ (PDPair fc hls p l@(PRef nfc hl n) t r)
            = case p of
                IsType -> asType
                IsTerm -> asValue
                TypeOrTerm ->
                   do compute
                      g <- goal
                      case g of
                         TType _ -> asType
                         _ -> asValue
         where asType = elab' ina (Just fc) (PApp fc (PRef NoFC hls sigmaTy)
                                        [pexp t,
                                         pexp (PLam fc n nfc Placeholder r)])
               asValue = elab' ina (Just fc) (PApp fc (PRef fc hls sigmaCon)
                                         [pimp (sMN 0 "a") t False,
                                          pimp (sMN 0 "P") Placeholder True,
                                          pexp l, pexp r])

    elab' ina _ (PDPair fc hls p l t r) = elab' ina (Just fc) (PApp fc (PRef fc hls sigmaCon)
                                                  [pimp (sMN 0 "a") t False,
                                                   pimp (sMN 0 "P") Placeholder True,
                                                   pexp l, pexp r])
    elab' ina fc (PAlternative ms (ExactlyOne delayok) as)
        = do as_pruned <- doPrune as
             -- Finish the mkUniqueNames job with the pruned set, rather than
             -- the full set.
             uns <- get_usedns
             let as' = map (mkUniqueNames (uns ++ map snd ms) ms) as_pruned
             (h : hs) <- get_holes
             ty <- goal
             case as' of
                  [] -> do hds <- mapM showHd as
                           lift $ tfail $ NoValidAlts hds
                  [x] -> elab' ina fc x
                  -- If there's options, try now, and if that fails, postpone
                  -- to later.
                  _ -> handleError isAmbiguous
                           (do hds <- mapM showHd as'
                               tryAll (zip (map (elab' ina fc) as')
                                           hds))
                        (do movelast h
                            delayElab 5 $ do
                              hs <- get_holes
                              when (h `elem` hs) $ do
                                  focus h
                                  as'' <- doPrune as'
                                  case as'' of
                                       [x] -> elab' ina fc x
                                       _ -> do hds <- mapM showHd as''
                                               tryAll' False (zip (map (elab' ina fc) as'')
                                                                  hds))
        where showHd (PApp _ (PRef _ _ (UN l)) [_, _, arg])
                 | l == txt "Delay" = showHd (getTm arg)
              showHd (PApp _ (PRef _ _ n) _) = return n
              showHd (PRef _ _ n) = return n
              showHd (PApp _ h _) = showHd h
              showHd (PHidden h) = showHd h
              showHd x = getNameFrom (sMN 0 "_") -- We probably should do something better than this here

              doPrune as =
                  do compute -- to get 'Delayed' if it's there
                     ty <- goal
                     ctxt <- get_context
                     env <- get_env
                     let ty' = unDelay ty
                     let (tc, _) = unApply ty'
                     return $ pruneByType eimpossible env tc ty' ist as

              unDelay t | (P _ (UN l) _, [_, arg]) <- unApply t,
                          l == txt "Delayed" = unDelay arg
                        | otherwise = t

              isAmbiguous (CantResolveAlts _) = delayok
              isAmbiguous (Elaborating _ _ _ e) = isAmbiguous e
              isAmbiguous (ElaboratingArg _ _ _ e) = isAmbiguous e
              isAmbiguous (At _ e) = isAmbiguous e
              isAmbiguous _ = False

    elab' ina fc (PAlternative ms FirstSuccess as_in)
        = do -- finish the mkUniqueNames job
             uns <- get_usedns
             let as = map (mkUniqueNames (uns ++ map snd ms) ms) as_in
             trySeq as
        where -- if none work, take the error from the first
              trySeq (x : xs) = let e1 = elab' ina fc x in
                                    try' e1 (trySeq' e1 xs) True
              trySeq [] = fail "Nothing to try in sequence"
              trySeq' deferr [] = do deferr; unifyProblems
              trySeq' deferr (x : xs)
                  = try' (tryCatch (do elab' ina fc x
                                       solveAutos ist fn False
                                       unifyProblems)
                             (\_ -> trySeq' deferr []))
                         (trySeq' deferr xs) True
    elab' ina fc (PAlternative ms TryImplicit (orig : alts)) = do
        env <- get_env
        compute
        ty <- goal
        let doelab = elab' ina fc orig
        tryCatch doelab
            (\err ->
                if recoverableErr err
                   then -- trace ("NEED IMPLICIT! " ++ show orig ++ "\n" ++
                        --      show alts ++ "\n" ++
                        --      showQuick err) $
                    -- Prune the coercions so that only the ones
                    -- with the right type to fix the error will be tried!
                    case pruneAlts err alts env of
                         [] -> lift $ tfail err
                         alts' -> do
                             try' (elab' ina fc (PAlternative ms (ExactlyOne False) alts'))
                                  (lift $ tfail err) -- take error from original if all fail
                                  True
                   else lift $ tfail err)
      where
        recoverableErr (CantUnify _ _ _ _ _ _) = True
        recoverableErr (TooManyArguments _) = False
        recoverableErr (CantSolveGoal _ _) = False
        recoverableErr (CantResolveAlts _) = False
        recoverableErr (NoValidAlts _) = True
        recoverableErr (ProofSearchFail (Msg _)) = True
        recoverableErr (ProofSearchFail _) = False
        recoverableErr (ElaboratingArg _ _ _ e) = recoverableErr e
        recoverableErr (At _ e) = recoverableErr e
        recoverableErr (ElabScriptDebug _ _ _) = False
        recoverableErr _ = True

        pruneAlts (CantUnify _ (inc, _) (outc, _) _ _ _) alts env
            = case unApply (normalise (tt_ctxt ist) env inc) of
                   (P (TCon _ _) n _, _) -> filter (hasArg n env) alts
                   (Constant _, _) -> alts
                   _ -> filter isLend alts -- special case hack for 'Borrowed'
        pruneAlts (ElaboratingArg _ _ _ e) alts env = pruneAlts e alts env
        pruneAlts (At _ e) alts env = pruneAlts e alts env
        pruneAlts (NoValidAlts as) alts env = alts
        pruneAlts err alts _ = filter isLend alts

        hasArg n env ap | isLend ap = True -- special case hack for 'Borrowed'
        hasArg n env (PApp _ (PRef _ _ a) _)
             = case lookupTyExact a (tt_ctxt ist) of
                    Just ty -> let args = map snd (getArgTys (normalise (tt_ctxt ist) env ty)) in
                                   any (fnIs n) args
                    Nothing -> False
        hasArg n env (PAlternative _ _ as) = any (hasArg n env) as
        hasArg n _ tm = False

        isLend (PApp _ (PRef _ _ l) _) = l == sNS (sUN "lend") ["Ownership"]
        isLend _ = False

        fnIs n ty = case unApply ty of
                         (P _ n' _, _) -> n == n'
                         _ -> False

        showQuick (CantUnify _ (l, _) (r, _) _ _ _)
            = show (l, r)
        showQuick (ElaboratingArg _ _ _ e) = showQuick e
        showQuick (At _ e) = showQuick e
        showQuick (ProofSearchFail (Msg _)) = "search fail"
        showQuick _ = "No chance"

    elab' ina _ (PPatvar fc n) | bindfree
        = do patvar n
             update_term liftPats
             highlightSource fc (AnnBoundName n False)
--    elab' (_, _, inty) (PRef fc f)
--       | isTConName f (tt_ctxt ist) && pattern && not reflection && not inty
--          = lift $ tfail (Msg "Typecase is not allowed")
    elab' ec fc' tm@(PRef fc hls n)
      | pattern && not reflection && not (e_qq ec) && not (e_intype ec)
            && isTConName n (tt_ctxt ist)
              = lift $ tfail $ Msg ("No explicit types on left hand side: " ++ show tm)
      | pattern && not reflection && not (e_qq ec) && e_nomatching ec
              = lift $ tfail $ Msg ("Attempting concrete match on polymorphic argument: " ++ show tm)
      | (pattern || intransform || (bindfree && bindable n)) && not (inparamBlock n) && not (e_qq ec)
        = do ty <- goal
             testImplicitWarning fc n ty
             let ina = e_inarg ec
                 guarded = e_guarded ec
                 inty = e_intype ec
             ctxt <- get_context
             env <- get_env

             -- If the name is defined, globally or locally, elaborate it
             -- as a reference, otherwise it might end up as a pattern var.
             let defined = case lookupTy n ctxt of
                               [] -> case lookupTyEnv n env of
                                          Just _ -> True
                                          _ -> False
                               _ -> True

             -- this is to stop us resolving interfaces recursively
             if (tcname n && ina && not intransform)
               then erun fc $
                      do patvar n
                         update_term liftPats
                         highlightSource fc (AnnBoundName n False)
               else if defined -- finally, ordinary PRef elaboration
                       then elabRef ec fc' fc hls n tm
                       else try (do apply (Var n) []
                                    annot <- findHighlight n
                                    solve
                                    highlightSource fc annot)
                                (do patvar n
                                    update_term liftPats
                                    highlightSource fc (AnnBoundName n False))
      where inparamBlock n = case lookupCtxtName n (inblock info) of
                                [] -> False
                                _ -> True
            bindable (NS _ _) = False
            bindable (MN _ _) = True
            bindable n = implicitable n && autoimpls
    elab' ina _ f@(PInferRef fc hls n) = elab' ina (Just fc) (PApp NoFC f [])
    elab' ina fc' tm@(PRef fc hls n)
          | pattern && not reflection && not (e_qq ina) && not (e_intype ina)
            && isTConName n (tt_ctxt ist)
              = lift $ tfail $ Msg ("No explicit types on left hand side: " ++ show tm)
          | pattern && not reflection && not (e_qq ina) && e_nomatching ina
              = lift $ tfail $ Msg ("Attempting concrete match on polymorphic argument: " ++ show tm)
          | otherwise = elabRef ina fc' fc hls n tm
    elab' ina _ (PLam _ _ _ _ PImpossible) = lift . tfail . Msg $ "Only pattern-matching lambdas can be impossible"
    elab' ina _ (PLam fc n nfc Placeholder sc)
          = do -- if n is a type constructor name, this makes no sense...
               ctxt <- get_context
               when (isTConName n ctxt) $
                    lift $ tfail (Msg $ "Can't use type constructor " ++ show n ++ " here")
               checkPiGoal n
               attack; intro (Just n);
               addPSname n -- okay for proof search
               -- trace ("------ intro " ++ show n ++ " ---- \n" ++ show ptm)
               elabE (ina { e_inarg = True } ) (Just fc) sc; solve
               highlightSource nfc (AnnBoundName n False)
    elab' ec _ (PLam fc n nfc ty sc)
          = do tyn <- getNameFrom (sMN 0 "lamty")
               -- if n is a type constructor name, this makes no sense...
               ctxt <- get_context
               when (isTConName n ctxt) $
                    lift $ tfail (Msg $ "Can't use type constructor " ++ show n ++ " here")
               checkPiGoal n
               claim tyn RType
               explicit tyn
               attack
               ptm <- get_term
               hs <- get_holes
               introTy (Var tyn) (Just n)
               addPSname n -- okay for proof search
               focus tyn

               elabE (ec { e_inarg = True, e_intype = True }) (Just fc) ty
               elabE (ec { e_inarg = True }) (Just fc) sc
               solve
               highlightSource nfc (AnnBoundName n False)
    elab' ina fc (PPi p n nfc Placeholder sc)
          = do attack;
               case pcount p of
                    RigW -> return ()
                    _ -> unless (LinearTypes `elem` idris_language_extensions ist
                                       || e_qq ina) $
                           lift $ tfail $ At nfc (Msg "You must turn on the LinearTypes extension to use a count")
               arg n (pcount p) (is_scoped p) (sMN 0 "phTy")
               addAutoBind p n
               addPSname n -- okay for proof search
               elabE (ina { e_inarg = True, e_intype = True }) fc sc
               solve
               highlightSource nfc (AnnBoundName n False)
    elab' ina fc (PPi p n nfc ty sc)
          = do attack; tyn <- getNameFrom (sMN 0 "piTy")
               claim tyn RType
               n' <- case n of
                        MN _ _ -> unique_hole n
                        _ -> return n
               case pcount p of
                    RigW -> return ()
                    _ -> unless (LinearTypes `elem` idris_language_extensions ist
                                       || e_qq ina) $
                           lift $ tfail $ At nfc (Msg "You must turn on the LinearTypes extension to use a linear argument")
               forall n' (pcount p) (is_scoped p) (Var tyn)
               addAutoBind p n'
               addPSname n' -- okay for proof search
               focus tyn
               let ec' = ina { e_inarg = True, e_intype = True }
               elabE ec' fc ty
               elabE ec' fc sc
               solve
               highlightSource nfc (AnnBoundName n False)
    elab' ina _ tm@(PLet fc n nfc ty val sc)
          = do attack
               ivs <- get_implementations
               tyn <- getNameFrom (sMN 0 "letty")
               claim tyn RType
               valn <- getNameFrom (sMN 0 "letval")
               claim valn (Var tyn)
               explicit valn
               letbind n (Var tyn) (Var valn)
               addPSname n
               case ty of
                   Placeholder -> return ()
                   _ -> do focus tyn
                           explicit tyn
                           elabE (ina { e_inarg = True, e_intype = True })
                                 (Just fc) ty
               focus valn
               elabE (ina { e_inarg = True, e_intype = True })
                     (Just fc) val
               ivs' <- get_implementations
               env <- get_env
               elabE (ina { e_inarg = True }) (Just fc) sc
               when (not (pattern || intransform)) $
                   mapM_ (\n -> do focus n
                                   g <- goal
                                   hs <- get_holes
                                   if all (\n -> n == tyn || not (n `elem` hs)) (freeNames g)
                                    then handleError (tcRecoverable emode)
                                           (resolveTC True False 10 g fn elabRec ist)
                                           (movelast n)
                                    else movelast n)
                         (ivs' \\ ivs)
               -- HACK: If the name leaks into its type, it may leak out of
               -- scope outside, so substitute in the outer scope.
               expandLet n (case lookupBinder n env of
                                 Just (Let t v) -> v
                                 other -> error ("Value not a let binding: " ++ show other))
               solve
               highlightSource nfc (AnnBoundName n False)
    elab' ina _ (PGoal fc r n sc) = do
         rty <- goal
         attack
         tyn <- getNameFrom (sMN 0 "letty")
         claim tyn RType
         valn <- getNameFrom (sMN 0 "letval")
         claim valn (Var tyn)
         letbind n (Var tyn) (Var valn)
         focus valn
         elabE (ina { e_inarg = True, e_intype = True }) (Just fc) (PApp fc r [pexp (delab ist rty)])
         env <- get_env
         computeLet n
         elabE (ina { e_inarg = True }) (Just fc) sc
         solve
--          elab' ina fc (PLet n Placeholder
--              (PApp fc r [pexp (delab ist rty)]) sc)
    elab' ina _ tm@(PApp fc (PInferRef _ _ f) args) = do
         rty <- goal
         ds <- get_deferred
         ctxt <- get_context
         -- make a function type a -> b -> c -> ... -> rty for the
         -- new function name
         env <- get_env
         argTys <- claimArgTys env args
         fn <- getNameFrom (sMN 0 "inf_fn")
         let fty = fnTy argTys rty
--             trace (show (ptm, map fst argTys)) $ focus fn
            -- build and defer the function application
         attack; deferType (mkN f) fty (map fst argTys); solve
         -- elaborate the arguments, to unify their types. They all have to
         -- be explicit.
         mapM_ elabIArg (zip argTys args)
       where claimArgTys env [] = return []
             claimArgTys env (arg : xs) | Just n <- localVar env (getTm arg)
                                  = do nty <- get_type (Var n)
                                       ans <- claimArgTys env xs
                                       return ((n, (False, forget nty)) : ans)
             claimArgTys env (_ : xs)
                                  = do an <- getNameFrom (sMN 0 "inf_argTy")
                                       aval <- getNameFrom (sMN 0 "inf_arg")
                                       claim an RType
                                       claim aval (Var an)
                                       ans <- claimArgTys env xs
                                       return ((aval, (True, (Var an))) : ans)
             fnTy [] ret  = forget ret
             fnTy ((x, (_, xt)) : xs) ret = RBind x (Pi RigW Nothing xt RType) (fnTy xs ret)

             localVar env (PRef _ _ x)
                           = case lookupBinder x env of
                                  Just _ -> Just x
                                  _ -> Nothing
             localVar env _ = Nothing

             elabIArg ((n, (True, ty)), def) =
               do focus n; elabE ina (Just fc) (getTm def)
             elabIArg _ = return () -- already done, just a name

             mkN n@(NS _ _) = n
             mkN n@(SN _) = n
             mkN n = case namespace info of
                          xs@(_:_) -> sNS n xs
                          _ -> n

    elab' ina _ (PMatchApp fc fn)
       = do (fn', imps) <- case lookupCtxtName fn (idris_implicits ist) of
                             [(n, args)] -> return (n, map (const True) args)
                             _ -> lift $ tfail (NoSuchVariable fn)
            ns <- match_apply (Var fn') (map (\x -> (x,0)) imps)
            solve
    -- if f is local, just do a simple_app
    -- FIXME: Anyone feel like refactoring this mess? - EB
    elab' ina topfc tm@(PApp fc (PRef ffc hls f) args_in)
      | pattern && not reflection && not (e_qq ina) && e_nomatching ina
              = lift $ tfail $ Msg ("Attempting concrete match on polymorphic argument: " ++ show tm)
      | otherwise = implicitApp $
         do env <- get_env
            ty <- goal
            fty <- get_type (Var f)
            ctxt <- get_context
            let dataCon = isDConName f ctxt
            annot <- findHighlight f
            knowns_m <- mapM getKnownImplicit args_in
            let knowns = mapMaybe id knowns_m
            args <- insertScopedImps fc f knowns (normalise ctxt env fty) args_in

            let unmatchableArgs = if pattern
                                     then getUnmatchable (tt_ctxt ist) f
                                     else []
--             trace ("BEFORE " ++ show f ++ ": " ++ show ty) $
            when (pattern && not reflection && not (e_qq ina) && not (e_intype ina)
                          && isTConName f (tt_ctxt ist)) $
              lift $ tfail $ Msg ("No explicit types on left hand side: " ++ show tm)
--             trace (show (f, args_in, args)) $
            if (f `elem` map fstEnv env && length args == 1 && length args_in == 1)
               then -- simple app, as below
                    do simple_app False
                                  (elabE (ina { e_isfn = True }) (Just fc) (PRef ffc hls f))
                                  (elabE (ina { e_inarg = True,
                                                e_guarded = dataCon }) (Just fc) (getTm (head args)))
                                  (show tm)
                       solve
                       mapM (uncurry highlightSource) $
                         (ffc, annot) : map (\f -> (f, annot)) hls
                       return []
               else
                 do ivs <- get_implementations
                    ps <- get_probs
                    -- HACK: we shouldn't resolve interfaces if we're defining an implementation
                    -- function or default definition.
                    let isinf = f == inferCon || tcname f
                    -- if f is an interface, we need to know its arguments so that
                    -- we can unify with them
                    case lookupCtxt f (idris_interfaces ist) of
                        [] -> return ()
                        _ -> do mapM_ setInjective (map getTm args)
                                -- maybe more things are solvable now
                                unifyProblems
                    let guarded = isConName f ctxt
--                    trace ("args is " ++ show args) $ return ()
                    ns <- apply (Var f) (map isph args)
--                    trace ("ns is " ++ show ns) $ return ()
                    -- mark any interface arguments as injective
--                     when (not pattern) $
                    mapM_ checkIfInjective (map snd ns)
                    unifyProblems -- try again with the new information,
                                  -- to help with disambiguation
                    ulog <- getUnifyLog

                    annot <- findHighlight f
                    mapM (uncurry highlightSource) $
                      (ffc, annot) : map (\f -> (f, annot)) hls

                    elabArgs ist (ina { e_inarg = e_inarg ina || not isinf,
                                        e_guarded = dataCon })
                           [] fc False f
                             (zip ns (unmatchableArgs ++ repeat False))
                             (f == sUN "Force")
                             (map (\x -> getTm x) args) -- TODO: remove this False arg
                    imp <- if (e_isfn ina) then
                              do guess <- get_guess
                                 env <- get_env
                                 case safeForgetEnv (map fstEnv env) guess of
                                      Nothing ->
                                         return []
                                      Just rguess -> do
                                         gty <- get_type rguess
                                         let ty_n = normalise ctxt env gty
                                         return $ getReqImps ty_n
                              else return []
                    -- Now we find out how many implicits we needed at the
                    -- end of the application by looking at the goal again
                    -- - Have another go, but this time add the
                    -- implicits (can't think of a better way than this...)
                    case imp of
                         rs@(_:_) | not pattern -> return rs -- quit, try again
                         _ -> do solve
                                 hs <- get_holes
                                 ivs' <- get_implementations
                                 -- Attempt to resolve any interfaces which have 'complete' types,
                                 -- i.e. no holes in them
                                 when (not pattern || (e_inarg ina && not tcgen)) $
                                    mapM_ (\n -> do focus n
                                                    g <- goal
                                                    env <- get_env
                                                    hs <- get_holes
                                                    if all (\n -> not (n `elem` hs)) (freeNames g)
                                                     then handleError (tcRecoverable emode)
                                                              (resolveTC False False 10 g fn elabRec ist)
                                                              (movelast n)
                                                     else movelast n)
                                          (ivs' \\ ivs)
                                 return []
      where
            -- Run the elaborator, which returns how many implicit
            -- args were needed, then run it again with those args. We need
            -- this because we have to elaborate the whole application to
            -- find out whether any computations have caused more implicits
            -- to be needed.
            implicitApp :: ElabD [ImplicitInfo] -> ElabD ()
            implicitApp elab
              | pattern || intransform = do elab; return ()
              | otherwise
                = do s <- get
                     imps <- elab
                     case imps of
                          [] -> return ()
                          es -> do put s
                                   elab' ina topfc (PAppImpl tm es)

            getKnownImplicit imp
                 | UnknownImp `elem` argopts imp
                    = return Nothing -- lift $ tfail $ UnknownImplicit (pname imp) f
                 | otherwise = return (Just (pname imp))

            getReqImps (Bind x (Pi _ (Just i) ty _) sc)
                 = i : getReqImps sc
            getReqImps _ = []

            checkIfInjective n = do
                env <- get_env
                case lookupBinder n env of
                     Nothing -> return ()
                     Just b ->
                       case unApply (normalise (tt_ctxt ist) env (binderTy b)) of
                            (P _ c _, args) ->
                                case lookupCtxtExact c (idris_interfaces ist) of
                                   Nothing -> return ()
                                   Just ci -> -- interface, set as injective
                                        do mapM_ setinjArg (getDets 0 (interface_determiners ci) args)
                                        -- maybe we can solve more things now...
                                           ulog <- getUnifyLog
                                           probs <- get_probs
                                           inj <- get_inj
                                           traceWhen ulog ("Injective now " ++ show args ++ "\nAll: " ++ show inj
                                                            ++ "\nProblems: " ++ qshow probs) $
                                             unifyProblems
                                           probs <- get_probs
                                           traceWhen ulog (qshow probs) $ return ()
                            _ -> return ()

            setinjArg (P _ n _) = setinj n
            setinjArg _ = return ()

            getDets i ds [] = []
            getDets i ds (a : as) | i `elem` ds = a : getDets (i + 1) ds as
                                  | otherwise = getDets (i + 1) ds as

            tacTm (PTactics _) = True
            tacTm (PProof _) = True
            tacTm _ = False

            setInjective (PRef _ _ n) = setinj n
            setInjective (PApp _ (PRef _ _ n) _) = setinj n
            setInjective _ = return ()

    elab' ina _ tm@(PApp fc f [arg]) =
            erun fc $
             do simple_app (not $ headRef f)
                           (elabE (ina { e_isfn = True }) (Just fc) f)
                           (elabE (ina { e_inarg = True }) (Just fc) (getTm arg))
                                (show tm)
                solve
        where headRef (PRef _ _ _) = True
              headRef (PApp _ f _) = headRef f
              headRef (PAlternative _ _ as) = all headRef as
              headRef _ = False

    elab' ina fc (PAppImpl f es) = do appImpl (reverse es) -- not that we look...
                                      solve
        where appImpl [] = elab' (ina { e_isfn = False }) fc f -- e_isfn not set, so no recursive expansion of implicits
              appImpl (e : es) = simple_app False
                                            (appImpl es)
                                            (elab' ina fc Placeholder)
                                            (show f)
    elab' ina fc Placeholder
        = do (h : hs) <- get_holes
             movelast h
    elab' ina fc (PMetavar nfc n) =
          do ptm <- get_term
             -- When building the metavar application, leave out the unique
             -- names which have been used elsewhere in the term, since we
             -- won't be able to use them in the resulting application.
             let unique_used = getUniqueUsed (tt_ctxt ist) ptm
             let n' = metavarName (namespace info) n
             attack
             psns <- getPSnames
             n' <- defer unique_used n'
             solve
             highlightSource nfc (AnnName n' (Just MetavarOutput) Nothing Nothing)
    elab' ina fc (PProof ts) = do compute; mapM_ (runTac True ist (elabFC info) fn) ts
    elab' ina fc (PTactics ts)
        | not pattern = do mapM_ (runTac False ist fc fn) ts
        | otherwise = elab' ina fc Placeholder
    elab' ina fc (PElabError e) = lift $ tfail e
    elab' ina mfc (PRewrite fc substfn rule sc newg)
        = elabRewrite (elab' ina mfc) ist fc substfn rule sc newg
    -- A common error case if trying to typecheck an autogenerated case block
    elab' ina _ c@(PCase fc Placeholder opts)
        = lift $ tfail (Msg "No expression for the case to inspect.\nYou need to replace the _ with an expression.")
    elab' ina _ c@(PCase fc scr opts)
        = do attack

             tyn <- getNameFrom (sMN 0 "scty")
             claim tyn RType
             valn <- getNameFrom (sMN 0 "scval")
             scvn <- getNameFrom (sMN 0 "scvar")
             claim valn (Var tyn)
             letbind scvn (Var tyn) (Var valn)

             -- Start filling in the scrutinee type, if we can work one
             -- out from the case options
             let scrTy = getScrType (map fst opts)
             case scrTy of
                  Nothing -> return ()
                  Just ty -> do focus tyn
                                elabE ina (Just fc) ty

             focus valn
             elabE (ina { e_inarg = True }) (Just fc) scr
             -- Solve any remaining implicits - we need to solve as many
             -- as possible before making the 'case' type
             unifyProblems
             matchProblems True
             args <- get_env
             envU <- mapM (getKind args) args
             let namesUsedInRHS = nub $ scvn : concatMap (\(_,rhs) -> allNamesIn rhs) opts

             -- Drop the unique arguments used in the term already
             -- and in the scrutinee (since it's
             -- not valid to use them again anyway)
             --
             -- Also drop unique arguments which don't appear explicitly
             -- in either case branch so they don't count as used
             -- unnecessarily (can only do this for unique things, since we
             -- assume they don't appear implicitly in types)
             ptm <- get_term
             let inOpts = (filter (/= scvn) (map fstEnv args)) \\ (concatMap (\x -> allNamesIn (snd x)) opts)

             let argsDropped = filter (\t -> isUnique envU t || isNotLift args t)
                                   (nub $ allNamesIn scr ++ inApp ptm ++
                                    inOpts)

             let args' = filter (\(n, _, _) -> n `notElem` argsDropped) args

             attack
             cname' <- defer argsDropped (mkN (mkCaseName fc fn))
             solve

             -- if the scrutinee is one of the 'args' in env, we should
             -- inspect it directly, rather than adding it as a new argument
             let newdef = PClauses fc [] cname'
                             (caseBlock fc cname' scr
                                (map (isScr scr) (reverse args')) opts)
             -- elaborate case
             updateAux (\e -> e { case_decls = (cname', newdef) : case_decls e } )
             -- if we haven't got the type yet, hopefully we'll get it later!
             movelast tyn
             solve
        where mkCaseName fc (NS n ns) = NS (mkCaseName fc n) ns
              mkCaseName fc n = SN (CaseN (FC' fc) n)
--               mkCaseName (UN x) = UN (x ++ "_case")
--               mkCaseName (MN i x) = MN i (x ++ "_case")
              mkN n@(NS _ _) = n
              mkN n = case namespace info of
                        xs@(_:_) -> sNS n xs
                        _ -> n

              getScrType [] = Nothing
              getScrType (f : os) = maybe (getScrType os) Just (getAppType f)

              getAppType (PRef _ _ n) =
                 case lookupTyName n (tt_ctxt ist) of
                      [(n', ty)] | isDConName n' (tt_ctxt ist) ->
                         case unApply (getRetTy ty) of
                           (P _ tyn _, args) ->
                               Just (PApp fc (PRef fc [] tyn)
                                    (map pexp (map (const Placeholder) args)))
                           _ -> Nothing
                      _ -> Nothing -- ambiguity is no help to us!
              getAppType (PApp _ t as) = getAppType t
              getAppType _ = Nothing

              inApp (P _ n _) = [n]
              inApp (App _ f a) = inApp f ++ inApp a
              inApp (Bind n (Let _ v) sc) = inApp v ++ inApp sc
              inApp (Bind n (Guess _ v) sc) = inApp v ++ inApp sc
              inApp (Bind n b sc) = inApp sc
              inApp _ = []

              isUnique envk n = case lookup n envk of
                                     Just u -> u
                                     _ -> False

              getKind env (n, _, _)
                  = case lookupBinder n env of
                         Nothing -> return (n, False) -- can't happen, actually...
                         Just b ->
                            do ty <- get_type (forget (binderTy b))
                               case ty of
                                    UType UniqueType -> return (n, True)
                                    UType AllTypes -> return (n, True)
                                    _ -> return (n, False)

              tcName tm | (P _ n _, _) <- unApply tm
                  = case lookupCtxt n (idris_interfaces ist) of
                         [_] -> True
                         _ -> False
              tcName _ = False

              isNotLift env n
                 = case lookupBinder n env of
                        Just ty ->
                             case unApply (binderTy ty) of
                                  (P _ n _, _) -> n `elem` noCaseLift info
                                  _ -> False
                        _ -> False

              usedIn ns (n, b)
                 = n `elem` ns
                     || any (\x -> x `elem` ns) (allTTNames (binderTy b))

    elab' ina fc (PUnifyLog t) = do unifyLog True
                                    elab' ina fc t
                                    unifyLog False
    elab' ina fc (PQuasiquote t goalt)
        = do -- First extract the unquoted subterms, replacing them with fresh
             -- names in the quasiquoted term. Claim their reflections to be
             -- an inferred type (to support polytypic quasiquotes).
             finalTy <- goal
             (t, unq) <- extractUnquotes 0 t
             let unquoteNames = map fst unq
             mapM_ (\uqn -> claim uqn (forget finalTy)) unquoteNames

             -- Save the old state - we need a fresh proof state to avoid
             -- capturing lexically available variables in the quoted term.
             ctxt <- get_context
             datatypes <- get_datatypes
             g_nextname <- get_global_nextname
             saveState
             updatePS (const .
                       newProof (sMN 0 "q") (constraintNS info) ctxt datatypes g_nextname $
                       P Ref (reflm "TT") Erased)

             -- Re-add the unquotes, letting Idris infer the (fictional)
             -- types. Here, they represent the real type rather than the type
             -- of their reflection.
             mapM_ (\n -> do ty <- getNameFrom (sMN 0 "unqTy")
                             claim ty RType
                             movelast ty
                             claim n (Var ty)
                             movelast n)
                   unquoteNames

             -- Determine whether there's an explicit goal type, and act accordingly
             -- Establish holes for the type and value of the term to be
             -- quasiquoted
             qTy <- getNameFrom (sMN 0 "qquoteTy")
             claim qTy RType
             movelast qTy
             qTm <- getNameFrom (sMN 0 "qquoteTm")
             claim qTm (Var qTy)

             -- Let-bind the result of elaborating the contained term, so that
             -- the hole doesn't disappear
             nTm <- getNameFrom (sMN 0 "quotedTerm")
             letbind nTm (Var qTy) (Var qTm)

             -- Fill out the goal type, if relevant
             case goalt of
               Nothing  -> return ()
               Just gTy -> do focus qTy
                              elabE (ina { e_qq = True }) fc gTy

             -- Elaborate the quasiquoted term into the hole
             focus qTm
             elabE (ina { e_qq = True }) fc t
             end_unify

             -- We now have an elaborated term. Reflect it and solve the
             -- original goal in the original proof state, preserving highlighting
             env <- get_env
             EState _ _ _ hs _ _ <- getAux
             loadState
             updateAux (\aux -> aux { highlighting = hs })

             let quoted = fmap (explicitNames . binderVal) $ lookupBinder nTm env
                 isRaw = case unApply (normaliseAll ctxt env finalTy) of
                           (P _ n _, []) | n == reflm "Raw" -> True
                           _ -> False
             case quoted of
               Just q -> do ctxt <- get_context
                            (q', _, _) <- lift $ recheck (constraintNS info) ctxt [(uq, RigW, Lam RigW Erased) | uq <- unquoteNames] (forget q) q
                            if pattern
                              then if isRaw
                                      then reflectRawQuotePattern unquoteNames (forget q')
                                      else reflectTTQuotePattern unquoteNames q'
                              else do if isRaw
                                        then -- we forget q' instead of using q to ensure rechecking
                                             fill $ reflectRawQuote unquoteNames (forget q')
                                        else fill $ reflectTTQuote unquoteNames q'
                                      solve

               Nothing -> lift . tfail . Msg $ "Broken elaboration of quasiquote"

             -- Finally fill in the terms or patterns from the unquotes. This
             -- happens last so that their holes still exist while elaborating
             -- the main quotation.
             mapM_ elabUnquote unq
      where elabUnquote (n, tm)
                = do focus n
                     elabE (ina { e_qq = False }) fc tm


    elab' ina fc (PUnquote t) = fail "Found unquote outside of quasiquote"
    elab' ina fc (PQuoteName n False nfc) =
      do fill $ reflectName n
         solve
    elab' ina fc (PQuoteName n True nfc) =
      do ctxt <- get_context
         env <- get_env
         case lookupBinder n env of
           Just _ -> do fill $ reflectName n
                        solve
                        highlightSource nfc (AnnBoundName n False)
           Nothing ->
             case lookupNameDef n ctxt of
               [(n', _)] -> do fill $ reflectName n'
                               solve
                               highlightSource nfc (AnnName n' Nothing Nothing Nothing)
               [] -> lift . tfail . NoSuchVariable $ n
               more -> lift . tfail . CantResolveAlts $ map fst more
    elab' ina fc (PAs _ n t) = lift . tfail . Msg $ "@-pattern not allowed here"
    elab' ina fc (PHidden t)
      | reflection = elab' ina fc t
      | otherwise
        = do (h : hs) <- get_holes
             -- Dotting a hole means that either the hole or any outer
             -- hole (a hole outside any occurrence of it)
             -- must be solvable by unification as well as being filled
             -- in directly.
             -- Delay dotted things to the end, then when we elaborate them
             -- we can check the result against what was inferred
             movelast h
             (h' : hs) <- get_holes
             -- If we're at the end anyway, do it now
             if h == h' then elabHidden h
                        else delayElab 10 $ elabHidden h
     where
      elabHidden h = do hs <- get_holes
                        when (h `elem` hs) $ do
                            focus h
                            dotterm
                            elab' ina fc t
    elab' ina fc (PRunElab fc' tm ns) =
      do unless (ElabReflection `elem` idris_language_extensions ist) $
           lift $ tfail $ At fc' (Msg "You must turn on the ElabReflection extension to use %runElab")
         attack
         let elabName = sNS (sUN "Elab") ["Elab", "Reflection", "Language"]
         n <- getNameFrom (sMN 0 "tacticScript")
         let scriptTy = RApp (Var elabName) (Var unitTy)
         claim n scriptTy
         focus n
         elabUnit <- goal
         attack -- to get an extra hole
         elab' ina (Just fc') tm
         script <- get_guess
         fullyElaborated script
         solve -- eliminate the hole. Because there are no references, the script is only in the binding
         ctxt <- get_context
         env <- get_env
         (scriptTm, scriptTy) <- lift $ check ctxt [] (forget script)
         lift $ converts ctxt env elabUnit scriptTy
         env <- get_env
         runElabAction info ist (maybe fc' id fc) env script ns
         solve
    elab' ina fc (PConstSugar constFC tm) =
      -- Here we elaborate the contained term, then calculate
      -- highlighting for constFC.  The highlighting is the
      -- highlighting for the outermost constructor of the result of
      -- evaluating the elaborated term, if one exists (it always
      -- should, but better to fail gracefully for something silly
      -- like highlighting info). This is how implicit applications of
      -- fromInteger get highlighted.
      do saveState -- so we don't pollute the elaborated term
         n <- getNameFrom (sMN 0 "cstI")
         n' <- getNameFrom (sMN 0 "cstIhole")
         g <- forget <$> goal
         claim n' g
         movelast n'
         -- In order to intercept the elaborated value, we need to
         -- let-bind it.
         attack
         letbind n g (Var n')
         focus n'
         elab' ina fc tm
         env <- get_env
         ctxt <- get_context
         let v = fmap (normaliseAll ctxt env . finalise . binderVal)
                      (lookupBinder n env)
         loadState -- we have the highlighting - re-elaborate the value
         elab' ina fc tm
         case v of
           Just val -> highlightConst constFC val
           Nothing -> return ()
       where highlightConst fc (P _ n _) =
               highlightSource fc (AnnName n Nothing Nothing Nothing)
             highlightConst fc (App _ f _) =
               highlightConst fc f
             highlightConst fc (Constant c) =
               highlightSource fc (AnnConst c)
             highlightConst _ _ = return ()
    elab' ina fc x = fail $ "Unelaboratable syntactic form " ++ showTmImpls x

    -- delay elaboration of 't', with priority 'pri' until after everything
    -- else is done.
    -- The delayed things with lower numbered priority will be elaborated
    -- first. (In practice, this means delayed alternatives, then PHidden
    -- things.)
    delayElab pri t
       = updateAux (\e -> e { delayed_elab = delayed_elab e ++ [(pri, t)] })

    isScr :: PTerm -> (Name, RigCount, Binder Term) -> (Name, (Bool, Binder Term))
    isScr (PRef _ _ n) (n', _, b) = (n', (n == n', b))
    isScr _ (n', _, b) = (n', (False, b))

    caseBlock :: FC -> Name
                 -> PTerm -- original scrutinee
                 -> [(Name, (Bool, Binder Term))] -> [(PTerm, PTerm)] -> [PClause]
    caseBlock fc n scr env opts
        = let args' = findScr env
              args = map mkarg (map getNmScr args') in
              map (mkClause args) opts

       where -- Find the variable we want as the scrutinee and mark it as
             -- 'True'. If the scrutinee is in the environment, match on that
             -- otherwise match on the new argument we're adding.
             findScr ((n, (True, t)) : xs)
                        = (n, (True, t)) : scrName n xs
             findScr [(n, (_, t))] = [(n, (True, t))]
             findScr (x : xs) = x : findScr xs
             -- [] can't happen since scrutinee is in the environment!
             findScr [] = error "The impossible happened - the scrutinee was not in the environment"

             -- To make sure top level pattern name remains in scope, put
             -- it at the end of the environment
             scrName n []  = []
             scrName n [(_, t)] = [(n, t)]
             scrName n (x : xs) = x : scrName n xs

             getNmScr (n, (s, _)) = (n, s)

             mkarg (n, s) = (PRef fc [] n, s)
             -- may be shadowed names in the new pattern - so replace the
             -- old ones with an _
             -- Also, names which don't appear on the rhs should not be
             -- fixed on the lhs, or this restricts the kind of matching
             -- we can do to non-dependent types.
             mkClause args (l, r)
                   = let args' = map (shadowed (allNamesIn l)) args
                         args'' = map (implicitable (allNamesIn r ++
                                                     keepscrName scr)) args'
                         lhs = PApp (getFC fc l) (PRef NoFC [] n)
                                 (map (mkLHSarg l) args'') in
                            PClause (getFC fc l) n lhs [] r []

             -- Keep scrutinee available if it's just a name (this makes
             -- the names in scope look better when looking at a hole on
             -- the rhs of a case)
             keepscrName (PRef _ _ n) = [n]
             keepscrName _ = []

             mkLHSarg l (tm, True) = pexp l
             mkLHSarg l (tm, False) = pexp tm

             shadowed new (PRef _ _ n, s) | n `elem` new = (Placeholder, s)
             shadowed new t = t

             implicitable rhs (PRef _ _ n, s) | n `notElem` rhs = (Placeholder, s)
             implicitable rhs t = t


    getFC d (PApp fc _ _) = fc
    getFC d (PRef fc _ _) = fc
    getFC d (PAlternative _ _ (x:_)) = getFC d x
    getFC d x = d

    -- Fail if a term is not yet fully elaborated (e.g. if it contains
    -- case block functions that don't yet exist)
    fullyElaborated :: Term -> ElabD ()
    fullyElaborated (P _ n _) =
      do estate <- getAux
         case lookup n (case_decls estate) of
           Nothing -> return ()
           Just _  -> lift . tfail $ ElabScriptStaging n
    fullyElaborated (Bind n b body) = fullyElaborated body >> for_ b fullyElaborated
    fullyElaborated (App _ l r) = fullyElaborated l >> fullyElaborated r
    fullyElaborated (Proj t _) = fullyElaborated t
    fullyElaborated _ = return ()

    -- If the goal type is a "Lazy", then try elaborating via 'Delay'
    -- first. We need to do this brute force approach, rather than anything
    -- more precise, since there may be various other ambiguities to resolve
    -- first.
    insertLazy :: ElabCtxt -> PTerm -> ElabD PTerm
    insertLazy ina t@(PApp _ (PRef _ _ (UN l)) _) | l == txt "Delay" = return t
    insertLazy ina t@(PApp _ (PRef _ _ (UN l)) _) | l == txt "Force" = return t
    insertLazy ina (PCoerced t) = return t
    -- Don't add a delay to top level pattern variables, since they
    -- can be forced on the rhs if needed
    insertLazy ina t@(PPatvar _ _) | pattern && not (e_guarded ina) = return t
    insertLazy ina t =
        do ty <- goal
           env <- get_env
           let (tyh, _) = unApply (normalise (tt_ctxt ist) env ty)
           let tries = [mkDelay env t, t]
           case tyh of
                P _ (UN l) _ | l == txt "Delayed"
                    -> return (PAlternative [] FirstSuccess tries)
                _ -> return t
      where
        mkDelay env (PAlternative ms b xs) = PAlternative ms b (map (mkDelay env) xs)
        mkDelay env t
            = let fc = fileFC "Delay" in
                  addImplBound ist (map fstEnv env) (PApp fc (PRef fc [] (sUN "Delay"))
                                                    [pexp t])


    -- Don't put implicit coercions around applications which are marked
    -- as '%noImplicit', or around case blocks, otherwise we get exponential
    -- blowup especially where there are errors deep in large expressions.
    notImplicitable (PApp _ f _) = notImplicitable f
    -- TMP HACK no coercing on bind (make this configurable)
    notImplicitable (PRef _ _ n)
        | [opts] <- lookupCtxt n (idris_flags ist)
            = NoImplicit `elem` opts
    notImplicitable (PAlternative _ _ as) = any notImplicitable as
    -- case is tricky enough without implicit coercions! If they are needed,
    -- they can go in the branches separately.
    notImplicitable (PCase _ _ _) = True
    notImplicitable _ = False

    -- Elaboration works more smoothly if we expand function applications
    -- to their full arity and elaborate it all at once (better error messages
    -- in particular)
    expandToArity tm@(PApp fc f a) = do
       env <- get_env
       case fullApp tm of
            -- if f is global, leave it alone because we've already
            -- expanded it to the right arity
            PApp fc ftm@(PRef _ _ f) args | Just aty <- lookupBinder f env ->
               do let a = length (getArgTys (normalise (tt_ctxt ist) env (binderTy aty)))
                  return (mkPApp fc a ftm args)
            _ -> return tm
    expandToArity t = return t

    fullApp (PApp _ (PApp fc f args) xs) = fullApp (PApp fc f (args ++ xs))
    fullApp x = x

    -- See if the name is listed as an implicit. If it is, return it, and
    -- drop it from the rest of the list
    findImplicit :: Name -> [PArg] -> (Maybe PArg, [PArg])
    findImplicit n [] = (Nothing, [])
    findImplicit n (i@(PImp _ _ _ n' _) : args)
        | n == n' = (Just i, args)
    findImplicit n (i@(PTacImplicit _ _ n' _ _) : args)
        | n == n' = (Just i, args)
    findImplicit n (x : xs) = let (arg, rest) = findImplicit n xs in
                                  (arg, x : rest)

    insertScopedImps :: FC -> Name -> [Name] -> Type -> [PArg] -> ElabD [PArg]
    insertScopedImps fc f knowns ty xs =
         do mapM_ (checkKnownImplicit (map fst (getArgTys ty) ++ knowns)) xs
            doInsert ty xs
      where
        doInsert ty@(Bind n (Pi _ im@(Just i) _ _) sc) xs
          | (Just arg, xs') <- findImplicit n xs,
            not (toplevel_imp i)
              = liftM (arg :) (doInsert sc xs')
          | tcimplementation i && not (toplevel_imp i)
              = liftM (pimp n (PResolveTC fc) True :) (doInsert sc xs)
          | not (toplevel_imp i)
              = liftM (pimp n Placeholder True :) (doInsert sc xs)
        doInsert (Bind n (Pi _ _ _ _) sc) (x : xs)
              = liftM (x :) (doInsert sc xs)
        doInsert ty xs = return xs

        -- Any implicit in the application needs to have the name of a
        -- scoped implicit or a top level implicit, otherwise report an error
        checkKnownImplicit ns imp@(PImp{})
             | pname imp `elem` ns = return ()
             | otherwise = lift $ tfail $ At fc $ UnknownImplicit (pname imp) f
        checkKnownImplicit ns _ = return ()

    insertImpLam ina t =
        do ty <- goal
           env <- get_env
           let ty' = normalise (tt_ctxt ist) env ty
           addLam ty' t
      where
        -- just one level at a time
        addLam goal@(Bind n (Pi _ (Just _) _ _) sc) t =
                 do impn <- unique_hole n -- (sMN 0 "scoped_imp")
                    return (PLam emptyFC impn NoFC Placeholder t)
        addLam _ t = return t

    insertCoerce ina t@(PCase _ _ _) = return t
    insertCoerce ina t | notImplicitable t = return t
    insertCoerce ina t =
        do ty <- goal
           -- Check for possible coercions to get to the goal
           -- and add them as 'alternatives'
           env <- get_env
           let ty' = normalise (tt_ctxt ist) env ty
           let cs = getCoercionsTo ist ty'
           let t' = case (t, cs) of
                         (PCoerced tm, _) -> tm
                         (_, []) -> t
                         (_, cs) -> PAlternative [] TryImplicit
                                         (t : map (mkCoerce env t) cs)
           return t'
       where
         mkCoerce env (PAlternative ms aty tms) n
             = PAlternative ms aty (map (\t -> mkCoerce env t n) tms)
         mkCoerce env t n = let fc = maybe (fileFC "Coercion") id (highestFC t) in
                                addImplBound ist (map fstEnv env)
                                  (PApp fc (PRef fc [] n) [pexp (PCoerced t)])

    elabRef :: ElabCtxt -> Maybe FC -> FC -> [FC] -> Name -> PTerm -> ElabD ()
    elabRef ina fc' fc hls n tm =
               do fty <- get_type (Var n) -- check for implicits
                  ctxt <- get_context
                  env <- get_env
                  a' <- insertScopedImps fc n [] (normalise ctxt env fty) []
                  if null a'
                     then erun fc $
                            do apply (Var n) []
                               hilite <- findHighlight n
                               solve
                               mapM_ (uncurry highlightSource) $
                                 (fc, hilite) : map (\f -> (f, hilite)) hls
                     else elab' ina fc' (PApp fc tm [])

    -- | Elaborate the arguments to a function
    elabArgs :: IState -- ^ The current Idris state
             -> ElabCtxt -- ^ (in an argument, guarded, in a type, in a qquote)
             -> [Bool]
             -> FC -- ^ Source location
             -> Bool
             -> Name -- ^ Name of the function being applied
             -> [((Name, Name), Bool)] -- ^ (Argument Name, Hole Name, unmatchable)
             -> Bool -- ^ under a 'force'
             -> [PTerm] -- ^ argument
             -> ElabD ()
    elabArgs ist ina failed fc retry f [] force _ = return ()
    elabArgs ist ina failed fc r f (((argName, holeName), unm):ns) force (t : args)
        = do hs <- get_holes
             if holeName `elem` hs then
                do focus holeName
                   case t of
                      Placeholder -> do movelast holeName
                                        elabArgs ist ina failed fc r f ns force args
                      _ -> elabArg t
                else elabArgs ist ina failed fc r f ns force args
      where elabArg t =
              do -- solveAutos ist fn False
                 now_elaborating fc f argName
                 wrapErr f argName $ do
                   hs <- get_holes
                   tm <- get_term
                   -- No coercing under an explicit Force (or it can Force/Delay
                   -- recursively!)
                   let elab = if force then elab' else elabE
                   failed' <- -- trace (show (n, t, hs, tm)) $
                              -- traceWhen (not (null cs)) (show ty ++ "\n" ++ showImp True t) $
                              do focus holeName;
                                 g <- goal
                                 -- Can't pattern match on polymorphic goals
                                 poly <- goal_polymorphic
                                 ulog <- getUnifyLog
                                 traceWhen ulog ("Elaborating argument " ++ show (argName, holeName, g)) $
                                  elab (ina { e_nomatching = unm && poly }) (Just fc) t
                                 return failed
                   done_elaborating_arg f argName
                   elabArgs ist ina failed fc r f ns force args
            wrapErr f argName action =
              do elabState <- get
                 while <- elaborating_app
                 let while' = map (\(x, y, z)-> (y, z)) while
                 (result, newState) <- case runStateT action elabState of
                                         OK (res, newState) -> return (res, newState)
                                         Error e -> do done_elaborating_arg f argName
                                                       lift (tfail (elaboratingArgErr while' e))
                 put newState
                 return result
    elabArgs _ _ _ _ _ _ (((arg, hole), _) : _) _ [] =
      fail $ "Can't elaborate these args: " ++ show arg ++ " " ++ show hole

    addAutoBind :: Plicity -> Name -> ElabD ()
    addAutoBind (Imp _ _ _ _ False _) n
         = updateAux (\est -> est { auto_binds = n : auto_binds est })
    addAutoBind _ _ = return ()

    testImplicitWarning :: FC -> Name -> Type -> ElabD ()
    testImplicitWarning fc n goal
       | implicitable n && emode == ETyDecl
           = do env <- get_env
                est <- getAux
                when (n `elem` auto_binds est) $
                    tryUnify env (lookupTyName n (tt_ctxt ist))
       | otherwise = return ()
      where
        tryUnify env [] = return ()
        tryUnify env ((nm, ty) : ts)
             = do inj <- get_inj
                  hs <- get_holes
                  case unify (tt_ctxt ist) env (ty, Nothing) (goal, Nothing)
                          inj hs [] [] of
                    OK _ ->
                       updateAux (\est -> est { implicit_warnings =
                                          (fc, nm) : implicit_warnings est })
                    _ -> tryUnify env ts

-- For every alternative, look at the function at the head. Automatically resolve
-- any nested alternatives where that function is also at the head

pruneAlt :: [PTerm] -> [PTerm]
pruneAlt xs = map prune xs
  where
    prune (PApp fc1 (PRef fc2 hls f) as)
        = PApp fc1 (PRef fc2 hls f) (fmap (fmap (choose f)) as)
    prune t = t

    choose f (PAlternative ms a as)
        = let as' = fmap (choose f) as
              fs = filter (headIs f) as' in
              case fs of
                 [a] -> a
                 _ -> PAlternative ms a as'

    choose f (PApp fc f' as) = PApp fc (choose f f') (fmap (fmap (choose f)) as)
    choose f t = t

    headIs f (PApp _ (PRef _ _ f') _) = f == f'
    headIs f (PApp _ f' _) = headIs f f'
    headIs f _ = True -- keep if it's not an application

-- | Use the local elab context to work out the highlighting for a name
findHighlight :: Name -> ElabD OutputAnnotation
findHighlight n = do ctxt <- get_context
                     env <- get_env
                     case lookupBinder n env of
                       Just _ -> return $ AnnBoundName n False
                       Nothing -> case lookupTyExact n ctxt of
                                    Just _ -> return $ AnnName n Nothing Nothing Nothing
                                    Nothing -> lift . tfail . InternalMsg $
                                                 "Can't find name " ++ show n

-- Try again to solve auto implicits
solveAuto :: IState -> Name -> Bool -> (Name, [FailContext]) -> ElabD ()
solveAuto ist fn ambigok (n, failc)
  = do hs <- get_holes
       when (not (null hs)) $ do
        env <- get_env
        g <- goal
        handleError cantsolve (when (n `elem` hs) $ do
                        focus n
                        isg <- is_guess -- if it's a guess, we're working on it recursively, so stop
                        when (not isg) $
                          proofSearch' ist True ambigok 100 True Nothing fn [] [])
             (lift $ Error (addLoc failc
                   (CantSolveGoal g (map (\(n, _, b) -> (n, binderTy b)) env))))
        return ()
  where addLoc (FailContext fc f x : prev) err
           = At fc (ElaboratingArg f x
                   (map (\(FailContext _ f' x') -> (f', x')) prev) err)
        addLoc _ err = err

        cantsolve (CantSolveGoal _ _) = True
        cantsolve (InternalMsg _) = True
        cantsolve (At _ e) = cantsolve e
        cantsolve (Elaborating _ _ _ e) = cantsolve e
        cantsolve (ElaboratingArg _ _ _ e) = cantsolve e
        cantsolve _ = False

solveAutos :: IState -> Name -> Bool -> ElabD ()
solveAutos ist fn ambigok
           = do autos <- get_autos
                mapM_ (solveAuto ist fn ambigok) (map (\(n, (fc, _)) -> (n, fc)) autos)

-- Return true if the given error suggests an interface failure is
-- recoverable
tcRecoverable :: ElabMode -> Err -> Bool
tcRecoverable ERHS (CantResolve f g _) = f
tcRecoverable ETyDecl (CantResolve f g _) = f
tcRecoverable e (ElaboratingArg _ _ _ err) = tcRecoverable e err
tcRecoverable e (At _ err) = tcRecoverable e err
tcRecoverable _ _ = True

trivial' ist
    = trivial (elab ist toplevel ERHS [] (sMN 0 "tac")) ist
trivialHoles' psn h ist
    = trivialHoles psn h (elab ist toplevel ERHS [] (sMN 0 "tac")) ist
proofSearch' ist rec ambigok depth prv top n psns hints
    = do unifyProblems
         proofSearch rec prv ambigok (not prv) depth
                     (elab ist toplevel ERHS [] (sMN 0 "tac")) top n psns hints ist
resolveTC' di mv depth tm n ist
    = resolveTC di mv depth tm n (elab ist toplevel ERHS [] (sMN 0 "tac")) ist

collectDeferred :: Maybe Name -> [Name] -> Context ->
                   Term -> State [(Name, (Int, Maybe Name, Type, [Name]))] Term
collectDeferred top casenames ctxt tm = cd [] tm
  where
    cd env (Bind n (GHole i psns t) app) =
        do ds <- get
           t' <- collectDeferred top casenames ctxt t
           when (not (n `elem` map fst ds)) $ put (ds ++ [(n, (i, top, t', psns))])
           cd env app
    cd env (Bind n b t)
         = do b' <- cdb b
              t' <- cd ((n, b) : env) t
              return (Bind n b' t')
      where
        cdb (Let t v)   = liftM2 Let (cd env t) (cd env v)
        cdb (Guess t v) = liftM2 Guess (cd env t) (cd env v)
        cdb b           = do ty' <- cd env (binderTy b)
                             return (b { binderTy = ty' })
    cd env (App s f a) = liftM2 (App s) (cd env f)
                                        (cd env a)
    cd env t = return t

case_ :: Bool -> Bool -> IState -> Name -> PTerm -> ElabD ()
case_ ind autoSolve ist fn tm = do
  attack
  tyn <- getNameFrom (sMN 0 "ity")
  claim tyn RType
  valn <- getNameFrom (sMN 0 "ival")
  claim valn (Var tyn)
  letn <- getNameFrom (sMN 0 "irule")
  letbind letn (Var tyn) (Var valn)
  focus valn
  elab ist toplevel ERHS [] (sMN 0 "tac") tm
  env <- get_env
  let (Just binding) = lookupBinder letn env
  let val = binderVal binding
  if ind then induction (forget val)
         else casetac (forget val)
  when autoSolve solveAll

-- | Compute the appropriate name for a top-level metavariable
metavarName :: [String] -> Name -> Name
metavarName _          n@(NS _ _) = n
metavarName (ns@(_:_)) n          = sNS n ns
metavarName _          n          = n

runElabAction :: ElabInfo -> IState -> FC -> Env -> Term -> [String] -> ElabD Term
runElabAction info ist fc env tm ns = do tm' <- eval tm
                                         runTacTm tm'

  where
    eval tm = do ctxt <- get_context
                 return $ normaliseAll ctxt env (finalise tm)

    returnUnit = return $ P (DCon 0 0 False) unitCon (P (TCon 0 0) unitTy Erased)

    patvars :: [(Name, Term)] -> Term -> ([(Name, Term)], Term)
    patvars ns (Bind n (PVar _ t) sc) = patvars ((n, t) : ns) (instantiate (P Bound n t) sc)
    patvars ns tm                   = (ns, tm)

    pullVars :: (Term, Term) -> ([(Name, Term)], Term, Term)
    pullVars (lhs, rhs) = (fst (patvars [] lhs), snd (patvars [] lhs), snd (patvars [] rhs)) -- TODO alpha-convert rhs

    requireError :: Err -> ElabD a -> ElabD ()
    requireError orErr elab =
      do state <- get
         case runStateT elab state of
           OK (_, state') -> lift (tfail orErr)
           Error e -> return ()

    -- create a fake TT term for the LHS of an impossible case
    fakeTT :: Raw -> Term
    fakeTT (Var n) =
      case lookupNameDef n (tt_ctxt ist) of
        [(n', TyDecl nt _)] -> P nt n' Erased
        _ -> P Ref n Erased
    fakeTT (RBind n b body) = Bind n (fmap fakeTT b) (fakeTT body)
    fakeTT (RApp f a) = App Complete (fakeTT f) (fakeTT a)
    fakeTT RType = TType (UVar [] (-1))
    fakeTT (RUType u) = UType u
    fakeTT (RConstant c) = Constant c

    defineFunction :: RFunDefn Raw -> ElabD ()
    defineFunction (RDefineFun n clauses) =
      do ctxt <- get_context
         ty <- maybe (fail "no type decl") return $ lookupTyExact n ctxt
         let info = CaseInfo True True False -- TODO document and figure out
         clauses' <- forM clauses (\case
                                      RMkFunClause lhs rhs ->
                                        do (lhs', lty) <- lift $ check ctxt [] lhs
                                           (rhs', rty) <- lift $ check ctxt [] rhs
                                           lift $ converts ctxt [] lty rty
                                           return $ Right (lhs', rhs')
                                      RMkImpossibleClause lhs ->
                                        do requireError (Msg "Not an impossible case") . lift $
                                             check ctxt [] lhs
                                           return $ Left (fakeTT lhs))
         let clauses'' = map (\case Right c -> pullVars c
                                    Left lhs -> let (ns, lhs') = patvars [] lhs
                                                in (ns, lhs', Impossible))
                            clauses'
         let clauses''' = map (\(ns, lhs, rhs) -> (map fst ns, lhs, rhs)) clauses''
         let argtys = map (\x -> (x, isCanonical x ctxt))
                          (map snd (getArgTys (normalise ctxt [] ty)))
         ctxt'<- lift $
                  addCasedef n (const [])
                             info False (STerm Erased)
                             True False -- TODO what are these?
                             argtys [] -- TODO inaccessible types
                             clauses'
                             clauses'''
                             clauses'''
                             ty
                             ctxt
         set_context ctxt'
         updateAux $ \e -> e { new_tyDecls = RClausesInstrs n clauses'' : new_tyDecls e}
         return ()


    checkClosed :: Raw -> Elab' aux (Term, Type)
    checkClosed tm = do ctxt <- get_context
                        (val, ty) <- lift $ check ctxt [] tm
                        return $! (finalise val, finalise ty)

    -- | Add another argument to a Pi
    mkPi :: RFunArg -> Raw -> Raw
    mkPi arg rTy = RBind (argName arg) (Pi RigW Nothing (argTy arg) (RUType AllTypes)) rTy

    mustBeType ctxt tm ty =
      case normaliseAll ctxt [] (finalise ty) of
        UType _ -> return ()
        TType _ -> return ()
        ty'    -> lift . tfail . InternalMsg $
                     show tm ++ " is not a type: it's " ++ show ty'

    mustNotBeDefined ctxt n =
      case lookupDefExact n ctxt of
        Just _ -> lift . tfail . InternalMsg $
                    show n ++ " is already defined."
        Nothing -> return ()

    -- | Prepare a constructor to be added to a datatype being defined here
    prepareConstructor :: Name -> RConstructorDefn -> ElabD (Name, [PArg], Type)
    prepareConstructor tyn (RConstructor cn args resTy) =
      do ctxt <- get_context
         -- ensure the constructor name is not qualified, and
         -- construct a qualified one
         notQualified cn
         let qcn = qualify cn

         -- ensure that the constructor name is not defined already
         mustNotBeDefined ctxt qcn

         -- construct the actual type for the constructor
         let cty = foldr mkPi resTy args
         (checkedTy, ctyTy) <- lift $ check ctxt [] cty
         mustBeType ctxt checkedTy ctyTy

         -- ensure that the constructor builds the right family
         case unApply (getRetTy (normaliseAll ctxt [] (finalise checkedTy))) of
           (P _ n _, _) | n == tyn -> return ()
           t -> lift . tfail . Msg $ "The constructor " ++ show cn ++
                                     " doesn't construct " ++ show tyn ++
                                     " (return type is " ++ show t ++ ")"

         -- add temporary type declaration for constructor (so it can
         -- occur in later constructor types)
         set_context (addTyDecl qcn (DCon 0 0 False) checkedTy ctxt)

         -- Save the implicits for high-level Idris
         let impls = map rFunArgToPArg args

         return (qcn, impls, checkedTy)

      where
        notQualified (NS _ _) = lift . tfail . Msg $ "Constructor names may not be qualified"
        notQualified _ = return ()

        qualify n = case tyn of
                      (NS _ ns) -> NS n ns
                      _ -> n

        getRetTy :: Type -> Type
        getRetTy (Bind _ (Pi _ _ _ _) sc) = getRetTy sc
        getRetTy ty = ty

    elabScriptStuck :: Term -> ElabD a
    elabScriptStuck x = lift . tfail $ ElabScriptStuck x


    -- Should be dependent
    tacTmArgs :: Int -> Term -> [Term] -> ElabD [Term]
    tacTmArgs l t args | length args == l = return args
                       | otherwise        = elabScriptStuck t -- Probably should be an argument size mismatch internal error


    -- | Do a step in the reflected elaborator monad. The input is the
    -- step, the output is the (reflected) term returned.
    runTacTm :: Term -> ElabD Term
    runTacTm tac@(unApply -> (P _ n _, args))
      | n == tacN "Prim__Solve"
      = do ~[] <- tacTmArgs 0 tac args -- patterns are irrefutable because `tacTmArgs` returns lists of exactly the size given to it as first argument
           solve
           returnUnit
      | n == tacN "Prim__Goal"
      = do ~[] <- tacTmArgs 0 tac args
           hs <- get_holes
           case hs of
             (h : _) -> do t <- goal
                           fmap fst . checkClosed $
                             rawPair (Var (reflm "TTName"), Var (reflm "TT"))
                                     (reflectName h,        reflect t)
             [] -> lift . tfail . Msg $
                     "Elaboration is complete. There are no goals."

      | n == tacN "Prim__Holes"
      = do ~[] <- tacTmArgs 0 tac args
           hs <- get_holes
           fmap fst . checkClosed $
             mkList (Var $ reflm "TTName") (map reflectName hs)
      | n == tacN "Prim__Guess"
      = do ~[] <- tacTmArgs 0 tac args
           g <- get_guess
           fmap fst . checkClosed $ reflect g
      | n == tacN "Prim__LookupTy"
      = do ~[name] <- tacTmArgs 1 tac args
           n' <- reifyTTName name
           ctxt <- get_context
           let getNameTypeAndType = \case Function ty _       -> (Ref, ty)
                                          TyDecl nt ty        -> (nt, ty)
                                          Operator ty _ _     -> (Ref, ty)
                                          CaseOp _ ty _ _ _ _ -> (Ref, ty)
               -- Idris tuples nest to the right
               reflectTriple (x, y, z) =
                 raw_apply (Var pairCon) [ Var (reflm "TTName")
                                         , raw_apply (Var pairTy) [Var (reflm "NameType"), Var (reflm "TT")]
                                         , x
                                         , raw_apply (Var pairCon) [ Var (reflm "NameType"), Var (reflm "TT")
                                                                   , y, z]]
           let defs = [ reflectTriple (reflectName n, reflectNameType nt, reflect ty)
                        | (n, def) <- lookupNameDef n' ctxt
                        , let (nt, ty) = getNameTypeAndType def ]
           fmap fst . checkClosed $
             rawList (raw_apply (Var pairTy) [ Var (reflm "TTName")
                                             , raw_apply (Var pairTy) [ Var (reflm "NameType")
                                                                       , Var (reflm "TT")]])
                     defs
      | n == tacN "Prim__LookupDatatype"
      = do ~[name] <- tacTmArgs 1 tac args
           n' <- reifyTTName name
           datatypes <- get_datatypes
           ctxt <- get_context
           fmap fst . checkClosed $
             rawList (Var (tacN "Datatype"))
                     (map reflectDatatype (buildDatatypes ist n'))
      | n == tacN "Prim__LookupFunDefn"
      = do ~[name] <- tacTmArgs 1 tac args
           n' <- reifyTTName name
           fmap fst . checkClosed $
             rawList (RApp (Var $ tacN "FunDefn") (Var $ reflm "TT"))
               (map reflectFunDefn (buildFunDefns ist n'))
      | n == tacN "Prim__LookupArgs"
      = do ~[name] <- tacTmArgs 1 tac args
           n' <- reifyTTName name
           let listTy = Var (sNS (sUN "List") ["List", "Prelude"])
               listFunArg = RApp listTy (Var (tacN "FunArg"))
            -- Idris tuples nest to the right
           let reflectTriple (x, y, z) =
                 raw_apply (Var pairCon) [ Var (reflm "TTName")
                                         , raw_apply (Var pairTy) [listFunArg, Var (reflm "Raw")]
                                         , x
                                         , raw_apply (Var pairCon) [listFunArg, Var (reflm "Raw")
                                                                   , y, z]]
           let out =
                 [ reflectTriple (reflectName fn, reflectList (Var (tacN "FunArg")) (map reflectArg args), reflectRaw res)
                 | (fn, pargs) <- lookupCtxtName n' (idris_implicits ist)
                 , (args, res) <- getArgs pargs . forget <$>
                                   maybeToList (lookupTyExact fn (tt_ctxt ist))
                 ]

           fmap fst . checkClosed $
             rawList (raw_apply (Var pairTy) [Var (reflm "TTName")
                                             , raw_apply (Var pairTy) [ RApp listTy
                                                                             (Var (tacN "FunArg"))
                                                                      , Var (reflm "Raw")]])
                     out
      | n == tacN "Prim__SourceLocation"
      = do ~[] <- tacTmArgs 0 tac args
           fmap fst . checkClosed $
             reflectFC fc
      | n == tacN "Prim__Namespace"
      = do ~[] <- tacTmArgs 0 tac args
           fmap fst . checkClosed $
             rawList (RConstant StrType) (map (RConstant . Str) ns)
      | n == tacN "Prim__Env"
      = do ~[] <- tacTmArgs 0 tac args
           env <- get_env
           fmap fst . checkClosed $ reflectEnv env
      | n == tacN "Prim__Fail"
      = do ~[_a, errs] <- tacTmArgs 2 tac args
           errs' <- eval errs
           parts <- reifyReportParts errs'
           lift . tfail $ ReflectionError [parts] (Msg "")
      | n == tacN "Prim__PureElab"
      = do ~[_a, tm] <- tacTmArgs 2 tac args
           return tm
      | n == tacN "Prim__BindElab"
      = do ~[_a, _b, first, andThen] <- tacTmArgs 4 tac args
           first' <- eval first
           res <- eval =<< runTacTm first'
           next <- eval (App Complete andThen res)
           runTacTm next
      | n == tacN "Prim__Try"
      = do ~[_a, first, alt] <- tacTmArgs 3 tac args
           first' <- eval first
           alt' <- eval alt
           try' (runTacTm first') (runTacTm alt') True
      | n == tacN "Prim__Fill"
      = do ~[raw] <- tacTmArgs 1 tac args
           raw' <- reifyRaw =<< eval raw
           apply raw' []
           returnUnit
      | n == tacN "Prim__Apply" || n == tacN "Prim__MatchApply"
      = do ~[raw, argSpec] <- tacTmArgs 2 tac args
           raw' <- reifyRaw =<< eval raw
           argSpec' <- map (\b -> (b, 0)) <$> reifyList reifyBool argSpec
           let op = if n == tacN "Prim__Apply"
                       then apply
                       else match_apply
           ns <- op raw' argSpec'
           fmap fst . checkClosed $
             rawList (rawPairTy (Var $ reflm "TTName") (Var $ reflm "TTName"))
                     [ rawPair (Var $ reflm "TTName", Var $ reflm "TTName")
                               (reflectName n1, reflectName n2)
                     | (n1, n2) <- ns
                     ]
      | n == tacN "Prim__Gensym"
      = do ~[hint] <- tacTmArgs 1 tac args
           hintStr <- eval hint
           case hintStr of
             Constant (Str h) -> do
               n <- getNameFrom (sMN 0 h)
               fmap fst $ get_type_val (reflectName n)
             _ -> fail "no hint"
      | n == tacN "Prim__Claim"
      = do ~[n, ty] <- tacTmArgs 2 tac args
           n' <- reifyTTName n
           ty' <- reifyRaw ty
           claim n' ty'
           returnUnit
      | n == tacN "Prim__Check"
      = do ~[env', raw] <- tacTmArgs 2 tac args
           env <- reifyEnv env'
           raw' <- reifyRaw =<< eval raw
           ctxt <- get_context
           (tm, ty) <- lift $ check ctxt env raw'
           fmap fst . checkClosed $
             rawPair (Var (reflm "TT"), Var (reflm "TT"))
                     (reflect tm,       reflect ty)
      | n == tacN "Prim__Attack"
      = do ~[] <- tacTmArgs 0 tac args
           attack
           returnUnit
      | n == tacN "Prim__Rewrite"
      = do ~[rule] <- tacTmArgs 1 tac args
           r <- reifyRaw rule
           rewrite r
           returnUnit
      | n == tacN "Prim__Focus"
      = do ~[what] <- tacTmArgs 1 tac args
           n' <- reifyTTName what
           hs <- get_holes
           if elem n' hs
              then focus n' >> returnUnit
              else lift . tfail . Msg $ "The name " ++ show n' ++ " does not denote a hole"
      | n == tacN "Prim__Unfocus"
      = do ~[what] <- tacTmArgs 1 tac args
           n' <- reifyTTName what
           movelast n'
           returnUnit
      | n == tacN "Prim__Intro"
      = do ~[mn] <- tacTmArgs 1 tac args
           n <- case fromTTMaybe mn of
                  Nothing -> return Nothing
                  Just name -> fmap Just $ reifyTTName name
           intro n
           returnUnit
      | n == tacN "Prim__Forall"
      = do ~[n, ty] <- tacTmArgs 2 tac args
           n' <- reifyTTName n
           ty' <- reifyRaw ty
           forall n' RigW Nothing ty'
           returnUnit
      | n == tacN "Prim__PatVar"
      = do ~[n] <- tacTmArgs 1 tac args
           n' <- reifyTTName n
           patvar' n'
           returnUnit
      | n == tacN "Prim__PatBind"
      = do ~[n] <- tacTmArgs 1 tac args
           n' <- reifyTTName n
           patbind n' RigW
           returnUnit
      | n == tacN "Prim__LetBind"
      = do ~[n, ty, tm] <- tacTmArgs 3 tac args
           n' <- reifyTTName n
           ty' <- reifyRaw ty
           tm' <- reifyRaw tm
           letbind n' ty' tm'
           returnUnit
      | n == tacN "Prim__Compute"
      = do ~[] <- tacTmArgs 0 tac args; compute ; returnUnit
      | n == tacN "Prim__Normalise"
      = do ~[env, tm] <- tacTmArgs 2 tac args
           env' <- reifyEnv env
           tm' <- reifyTT tm
           ctxt <- get_context
           let out = normaliseAll ctxt env' (finalise tm')
           fmap fst . checkClosed $ reflect out
      | n == tacN "Prim__Whnf"
      = do ~[tm] <- tacTmArgs 1 tac args
           tm' <- reifyTT tm
           ctxt <- get_context
           fmap fst . checkClosed . reflect $ whnf ctxt [] tm'
      | n == tacN "Prim__Converts"
      = do ~[env, tm1, tm2] <- tacTmArgs 3 tac args
           env' <- reifyEnv env
           tm1' <- reifyTT tm1
           tm2' <- reifyTT tm2
           ctxt <- get_context
           lift $ converts ctxt env' tm1' tm2'
           returnUnit
      | n == tacN "Prim__DeclareType"
      = do ~[decl] <- tacTmArgs 1 tac args
           (RDeclare n args res) <- reifyTyDecl decl
           ctxt <- get_context
           let rty = foldr mkPi res args
           (checked, ty') <- lift $ check ctxt [] rty
           mustBeType ctxt checked ty'
           mustNotBeDefined ctxt n
           let decl = TyDecl Ref checked
               ctxt' = addCtxtDef n decl ctxt
           set_context ctxt'
           updateAux $ \e -> e { new_tyDecls = (RTyDeclInstrs n fc (map rFunArgToPArg args) checked) :
                                               new_tyDecls e }
           returnUnit
      | n == tacN "Prim__DefineFunction"
      = do ~[decl] <- tacTmArgs 1 tac args
           defn <- reifyFunDefn decl
           defineFunction defn
           returnUnit
      | n == tacN "Prim__DeclareDatatype"
      = do ~[decl] <- tacTmArgs 1 tac args
           RDeclare n args resTy <- reifyTyDecl decl
           ctxt <- get_context
           let tcTy = foldr mkPi resTy args
           (checked, ty') <- lift $ check ctxt [] tcTy
           mustBeType ctxt checked ty'
           mustNotBeDefined ctxt n
           let ctxt' = addTyDecl n (TCon 0 0) checked ctxt
           set_context ctxt'
           updateAux $ \e -> e { new_tyDecls = RDatatypeDeclInstrs n (map rFunArgToPArg args) : new_tyDecls e }
           returnUnit
      | n == tacN "Prim__DefineDatatype"
      = do ~[defn] <- tacTmArgs 1 tac args
           RDefineDatatype n ctors <- reifyRDataDefn defn
           ctxt <- get_context
           tyconTy <- case lookupTyExact n ctxt of
                        Just t -> return t
                        Nothing -> lift . tfail . Msg $ "Type not previously declared"
           datatypes <- get_datatypes
           case lookupCtxtName n datatypes of
             [] -> return ()
             _  -> lift . tfail . Msg $ show n ++ " is already defined as a datatype."
           -- Prepare the constructors
           ctors' <- mapM (prepareConstructor n) ctors
           ttag <- do ES (ps, aux) str prev <- get
                      let i = global_nextname ps
                      put $ ES (ps { global_nextname = global_nextname ps + 1 },
                                aux)
                               str
                               prev
                      return i
           let ctxt' = addDatatype (Data n ttag tyconTy False (map (\(cn, _, cty) -> (cn, cty)) ctors')) ctxt
           set_context ctxt'
           -- the rest happens in a bit
           updateAux $ \e -> e { new_tyDecls = RDatatypeDefnInstrs n tyconTy ctors' : new_tyDecls e }
           returnUnit
      | n == tacN "Prim__AddImplementation"
      = do ~[cls, impl] <- tacTmArgs 2 tac args
           interfaceName <- reifyTTName cls
           implName <- reifyTTName impl
           updateAux $ \e -> e { new_tyDecls = RAddImplementation interfaceName implName :
                                               new_tyDecls e }
           returnUnit
      | n == tacN "Prim__IsTCName"
      = do ~[n] <- tacTmArgs 1 tac args
           n' <- reifyTTName n
           case lookupCtxtExact n' (idris_interfaces ist) of
             Just _ -> fmap fst . checkClosed $ Var (sNS (sUN "True") ["Bool", "Prelude"])
             Nothing -> fmap fst . checkClosed $ Var (sNS (sUN "False") ["Bool", "Prelude"])
      | n == tacN "Prim__ResolveTC"
      = do ~[fn] <- tacTmArgs 1 tac args
           g <- goal
           fn <- reifyTTName fn
           resolveTC' False True 100 g fn ist
           returnUnit
      | n == tacN "Prim__Search"
      = do ~[depth, hints] <- tacTmArgs 2 tac args
           d <- eval depth
           hints' <- eval hints
           case (d, unList hints') of
             (Constant (I i), Just hs) ->
               do actualHints <- mapM reifyTTName hs
                  unifyProblems
                  let psElab = elab ist toplevel ERHS [] (sMN 0 "tac")
                  proofSearch True True False False i psElab Nothing (sMN 0 "search ") [] actualHints ist
                  returnUnit
             (Constant (I _), Nothing ) ->
               lift . tfail . InternalMsg $ "Not a list: " ++ show hints'
             (_, _) -> lift . tfail . InternalMsg $ "Can't reify int " ++ show d
      | n == tacN "Prim__RecursiveElab"
      = do ~[goal, script] <- tacTmArgs 2 tac args
           goal' <- reifyRaw goal
           ctxt <- get_context
           script <- eval script
           (goalTT, goalTy) <- lift $ check ctxt [] goal'
           lift $ isType ctxt [] goalTy
           recH <- getNameFrom (sMN 0 "recElabHole")
           aux <- getAux
           datatypes <- get_datatypes
           env <- get_env
           g_next <- get_global_nextname

           (ctxt', ES (p, aux') _ _) <-
              do (ES (current_p, _) _ _) <- get
                 lift $ runElab aux
                             (do runElabAction info ist fc [] script ns
                                 ctxt' <- get_context
                                 return ctxt')
                             ((newProof recH (constraintNS info) ctxt datatypes g_next goalTT)
                              { nextname = nextname current_p })
           set_context ctxt'

           let tm_out = getProofTerm (pterm p)
           do (ES (prf, _) s e) <- get
              let p' = prf { nextname = nextname p
                           , global_nextname = global_nextname p
                           }
              put (ES (p', aux') s e)
           env' <- get_env
           (tm, ty, _) <- lift $ recheck (constraintNS info) ctxt' env (forget tm_out) tm_out
           let (tm', ty') = (reflect tm, reflect ty)
           fmap fst . checkClosed $
             rawPair (Var $ reflm "TT", Var $ reflm "TT")
                     (tm', ty')
      | n == tacN "Prim__Metavar"
      = do ~[n] <- tacTmArgs 1 tac args
           n' <- reifyTTName n
           ctxt <- get_context
           ptm <- get_term
           -- See documentation above in the elab case for PMetavar
           let unique_used = getUniqueUsed ctxt ptm
           let mvn = metavarName ns n'
           attack
           defer unique_used mvn
           solve
           returnUnit
      | n == tacN "Prim__Fixity"
      = do ~[op'] <- tacTmArgs 1 tac args
           opTm <- eval op'
           case opTm of
             Constant (Str op) ->
               let opChars = ":!#$%&*+./<=>?@\\^|-~"
                   invalidOperators = [":", "=>", "->", "<-", "=", "?=", "|", "**", "==>", "\\", "%", "~", "?", "!"]
                   fixities = idris_infixes ist
               in if not (all (flip elem opChars) op) || elem op invalidOperators
                     then lift . tfail . Msg $ "'" ++ op ++ "' is not a valid operator name."
                     else case nub [f | Fix f someOp <- fixities, someOp == op] of
                            []   -> lift . tfail . Msg $ "No fixity found for operator '" ++ op ++ "'."
                            [f]  -> fmap fst . checkClosed $ reflectFixity f
                            many -> lift . tfail . InternalMsg $ "Ambiguous fixity for '" ++ op ++ "'!  Found " ++ show many
             _ -> lift . tfail . Msg $ "Not a constant string for an operator name: " ++ show opTm
      | n == tacN "Prim__Debug"
      = do ~[ty, msg] <- tacTmArgs 2 tac args
           msg' <- eval msg
           parts <- reifyReportParts msg
           debugElaborator parts
    runTacTm x = elabScriptStuck x

-- Running tactics directly
-- if a tactic adds unification problems, return an error

runTac :: Bool -> IState -> Maybe FC -> Name -> PTactic -> ElabD ()
runTac autoSolve ist perhapsFC fn tac
    = do env <- get_env
         g <- goal
         let tac' = fmap (addImplBound ist (map fstEnv env)) tac
         if autoSolve
            then runT tac'
            else no_errors (runT tac')
                   (Just (CantSolveGoal g (map (\(n, _, b) -> (n, binderTy b)) env)))
  where
    runT (Intro []) = do g <- goal
                         attack; intro (bname g)
      where
        bname (Bind n _ _) = Just n
        bname _ = Nothing
    runT (Intro xs) = mapM_ (\x -> do attack; intro (Just x)) xs
    runT Intros = do g <- goal
                     attack;
                     intro (bname g)
                     try' (runT Intros)
                          (return ()) True
      where
        bname (Bind n _ _) = Just n
        bname _ = Nothing
    runT (Exact tm) = do elab ist toplevel ERHS [] (sMN 0 "tac") tm
                         when autoSolve solveAll
    runT (MatchRefine fn)
        = do fnimps <-
               case lookupCtxtName fn (idris_implicits ist) of
                    [] -> do a <- envArgs fn
                             return [(fn, a)]
                    ns -> return (map (\ (n, a) -> (n, map (const True) a)) ns)
             let tacs = map (\ (fn', imps) ->
                                 (match_apply (Var fn') (map (\x -> (x, 0)) imps),
                                     fn')) fnimps
             tryAll tacs
             when autoSolve solveAll
       where envArgs n = do e <- get_env
                            case lookupBinder n e of
                               Just t -> return $ map (const False)
                                                      (getArgTys (binderTy t))
                               _ -> return []
    runT (Refine fn [])
        = do fnimps <-
               case lookupCtxtName fn (idris_implicits ist) of
                    [] -> do a <- envArgs fn
                             return [(fn, a)]
                    ns -> return (map (\ (n, a) -> (n, map isImp a)) ns)
             let tacs = map (\ (fn', imps) ->
                                 (apply (Var fn') (map (\x -> (x, 0)) imps),
                                     fn')) fnimps
             tryAll tacs
             when autoSolve solveAll
       where isImp (PImp _ _ _ _ _) = True
             isImp _ = False
             envArgs n = do e <- get_env
                            case lookupBinder n e of
                               Just t -> return $ map (const False)
                                                      (getArgTys (binderTy t))
                               _ -> return []
    runT (Refine fn imps) = do ns <- apply (Var fn) (map (\x -> (x,0)) imps)
                               when autoSolve solveAll
    runT DoUnify = do unify_all
                      when autoSolve solveAll
    runT (Claim n tm) = do tmHole <- getNameFrom (sMN 0 "newGoal")
                           claim tmHole RType
                           claim n (Var tmHole)
                           focus tmHole
                           elab ist toplevel ERHS [] (sMN 0 "tac") tm
                           focus n
    runT (Equiv tm) -- let bind tm, then
              = do attack
                   tyn <- getNameFrom (sMN 0 "ety")
                   claim tyn RType
                   valn <- getNameFrom (sMN 0 "eqval")
                   claim valn (Var tyn)
                   letn <- getNameFrom (sMN 0 "equiv_val")
                   letbind letn (Var tyn) (Var valn)
                   focus tyn
                   elab ist toplevel ERHS [] (sMN 0 "tac") tm
                   focus valn
                   when autoSolve solveAll
    runT (Rewrite tm) -- to elaborate tm, let bind it, then rewrite by that
              = do attack; -- (h:_) <- get_holes
                   tyn <- getNameFrom (sMN 0 "rty")
                   -- start_unify h
                   claim tyn RType
                   valn <- getNameFrom (sMN 0 "rval")
                   claim valn (Var tyn)
                   letn <- getNameFrom (sMN 0 "rewrite_rule")
                   letbind letn (Var tyn) (Var valn)
                   focus valn
                   elab ist toplevel ERHS [] (sMN 0 "tac") tm
                   rewrite (Var letn)
                   when autoSolve solveAll
    runT (Induction tm) -- let bind tm, similar to the others
              = case_ True autoSolve ist fn tm
    runT (CaseTac tm)
              = case_ False autoSolve ist fn tm
    runT (LetTac n tm)
              = do attack
                   tyn <- getNameFrom (sMN 0 "letty")
                   claim tyn RType
                   valn <- getNameFrom (sMN 0 "letval")
                   claim valn (Var tyn)
                   letn <- unique_hole n
                   letbind letn (Var tyn) (Var valn)
                   focus valn
                   elab ist toplevel ERHS [] (sMN 0 "tac") tm
                   when autoSolve solveAll
    runT (LetTacTy n ty tm)
              = do attack
                   tyn <- getNameFrom (sMN 0 "letty")
                   claim tyn RType
                   valn <- getNameFrom (sMN 0 "letval")
                   claim valn (Var tyn)
                   letn <- unique_hole n
                   letbind letn (Var tyn) (Var valn)
                   focus tyn
                   elab ist toplevel ERHS [] (sMN 0 "tac") ty
                   focus valn
                   elab ist toplevel ERHS [] (sMN 0 "tac") tm
                   when autoSolve solveAll
    runT Compute = compute
    runT Trivial = do trivial' ist; when autoSolve solveAll
    runT TCImplementation = runT (Exact (PResolveTC emptyFC))
    runT (ProofSearch rec prover depth top psns hints)
         = do proofSearch' ist rec False depth prover top fn psns hints
              when autoSolve solveAll
    runT (Focus n) = focus n
    runT Unfocus = do hs <- get_holes
                      case hs of
                        []      -> return ()
                        (h : _) -> movelast h
    runT Solve = solve
    runT (Try l r) = do try' (runT l) (runT r) True
    runT (TSeq l r) = do runT l; runT r
    runT (ApplyTactic tm) = do tenv <- get_env -- store the environment
                               tgoal <- goal -- store the goal
                               attack -- let f : List (TTName, Binder TT) -> TT -> Tactic = tm in ...
                               script <- getNameFrom (sMN 0 "script")
                               claim script scriptTy
                               scriptvar <- getNameFrom (sMN 0 "scriptvar" )
                               letbind scriptvar scriptTy (Var script)
                               focus script
                               elab ist toplevel ERHS [] (sMN 0 "tac") tm
                               (script', _) <- get_type_val (Var scriptvar)
                               -- now that we have the script apply
                               -- it to the reflected goal and context
                               restac <- getNameFrom (sMN 0 "restac")
                               claim restac tacticTy
                               focus restac
                               fill (raw_apply (forget script')
                                               [reflectEnv tenv, reflect tgoal])
                               restac' <- get_guess
                               solve
                               -- normalise the result in order to
                               -- reify it
                               ctxt <- get_context
                               env <- get_env
                               let tactic = normalise ctxt env restac'
                               runReflected tactic
        where tacticTy = Var (reflm "Tactic")
              listTy = Var (sNS (sUN "List") ["List", "Prelude"])
              scriptTy = (RBind (sMN 0 "__pi_arg")
                                (Pi RigW Nothing (RApp listTy envTupleType) RType)
                                    (RBind (sMN 1 "__pi_arg")
                                           (Pi RigW Nothing (Var $ reflm "TT") RType) tacticTy))
    runT (ByReflection tm) -- run the reflection function 'tm' on the
                           -- goal, then apply the resulting reflected Tactic
        = do tgoal <- goal
             attack
             script <- getNameFrom (sMN 0 "script")
             claim script scriptTy
             scriptvar <- getNameFrom (sMN 0 "scriptvar" )
             letbind scriptvar scriptTy (Var script)
             focus script
             ptm <- get_term
             env <- get_env
             let denv = map (\(n, _, b) -> (n, binderTy b)) env
             elab ist toplevel ERHS [] (sMN 0 "tac")
                  (PApp emptyFC tm [pexp (delabTy' ist [] denv tgoal True True True)])
             (script', _) <- get_type_val (Var scriptvar)
             -- now that we have the script apply
             -- it to the reflected goal
             restac <- getNameFrom (sMN 0 "restac")
             claim restac tacticTy
             focus restac
             fill (forget script')
             restac' <- get_guess
             solve
             -- normalise the result in order to
             -- reify it
             ctxt <- get_context
             env <- get_env
             let tactic = normalise ctxt env restac'
             runReflected tactic
      where tacticTy = Var (reflm "Tactic")
            scriptTy = tacticTy

    runT (Reflect v) = do attack -- let x = reflect v in ...
                          tyn <- getNameFrom (sMN 0 "letty")
                          claim tyn RType
                          valn <- getNameFrom (sMN 0 "letval")
                          claim valn (Var tyn)
                          letn <- getNameFrom (sMN 0 "letvar")
                          letbind letn (Var tyn) (Var valn)
                          focus valn
                          elab ist toplevel ERHS [] (sMN 0 "tac") v
                          (value, _) <- get_type_val (Var letn)
                          ctxt <- get_context
                          env <- get_env
                          let value' = normalise ctxt env value
                          runTac autoSolve ist perhapsFC fn (Exact $ PQuote (reflect value'))
    runT (Fill v) = do attack -- let x = fill x in ...
                       tyn <- getNameFrom (sMN 0 "letty")
                       claim tyn RType
                       valn <- getNameFrom (sMN 0 "letval")
                       claim valn (Var tyn)
                       letn <- getNameFrom (sMN 0 "letvar")
                       letbind letn (Var tyn) (Var valn)
                       focus valn
                       elab ist toplevel ERHS [] (sMN 0 "tac") v
                       (value, _) <- get_type_val (Var letn)
                       ctxt <- get_context
                       env <- get_env
                       let value' = normalise ctxt env value
                       rawValue <- reifyRaw value'
                       runTac autoSolve ist perhapsFC fn (Exact $ PQuote rawValue)
    runT (GoalType n tac) = do g <- goal
                               case unApply g of
                                    (P _ n' _, _) ->
                                       if nsroot n' == sUN n
                                          then runT tac
                                          else fail "Wrong goal type"
                                    _ -> fail "Wrong goal type"
    runT ProofState = do g <- goal
                         return ()
    runT Skip = return ()
    runT (TFail err) = lift . tfail $ ReflectionError [err] (Msg "")
    runT SourceFC =
      case perhapsFC of
        Nothing -> lift . tfail $ Msg "There is no source location available."
        Just fc ->
          do fill $ reflectFC fc
             solve
    runT Qed = lift . tfail $ Msg "The qed command is only valid in the interactive prover"
    runT x = fail $ "Not implemented " ++ show x

    runReflected t = do t' <- reify ist t
                        runTac autoSolve ist perhapsFC fn t'

elaboratingArgErr :: [(Name, Name)] -> Err -> Err
elaboratingArgErr [] err = err
elaboratingArgErr ((f,x):during) err = fromMaybe err (rewrite err)
  where rewrite (ElaboratingArg _ _ _ _) = Nothing
        rewrite (ProofSearchFail e) = fmap ProofSearchFail (rewrite e)
        rewrite (At fc e) = fmap (At fc) (rewrite e)
        rewrite err = Just (ElaboratingArg f x during err)


withErrorReflection :: Idris a -> Idris a
withErrorReflection x = idrisCatch x (\ e -> handle e >>= ierror)
    where handle :: Err -> Idris Err
          handle e@(ReflectionError _ _)  = do logElab 3 "Skipping reflection of error reflection result"
                                               return e -- Don't do meta-reflection of errors
          handle e@(ReflectionFailed _ _) = do logElab 3 "Skipping reflection of reflection failure"
                                               return e
          -- At and Elaborating are just plumbing - error reflection shouldn't rewrite them
          handle e@(At fc err) = do logElab 3 "Reflecting body of At"
                                    err' <- handle err
                                    return (At fc err')
          handle e@(Elaborating what n ty err) = do logElab 3 "Reflecting body of Elaborating"
                                                    err' <- handle err
                                                    return (Elaborating what n ty err')
          handle e@(ElaboratingArg f a prev err) = do logElab 3 "Reflecting body of ElaboratingArg"
                                                      hs <- getFnHandlers f a
                                                      err' <- if null hs
                                                                 then handle err
                                                                 else applyHandlers err hs
                                                      return (ElaboratingArg f a prev err')
          -- ProofSearchFail is an internal detail - so don't expose it
          handle (ProofSearchFail e) = handle e
          -- TODO: argument-specific error handlers go here for ElaboratingArg
          handle e = do ist <- getIState
                        logElab 2 "Starting error reflection"
                        logElab 5 (show e)
                        let handlers = idris_errorhandlers ist
                        applyHandlers e handlers
          getFnHandlers :: Name -> Name -> Idris [Name]
          getFnHandlers f arg = do ist <- getIState
                                   let funHandlers = maybe M.empty id .
                                                     lookupCtxtExact f .
                                                     idris_function_errorhandlers $ ist
                                   return . maybe [] S.toList . M.lookup arg $ funHandlers


          applyHandlers e handlers =
                      do ist <- getIState
                         let err = fmap (errReverse ist) e
                         logElab 3 $ "Using reflection handlers " ++
                                    concat (intersperse ", " (map show handlers))
                         let reports = map (\n -> RApp (Var n) (reflectErr err)) handlers

                         -- Typecheck error handlers - if this fails, then something else was wrong earlier!
                         handlers <- case mapM (check (tt_ctxt ist) []) reports of
                                       Error e -> ierror $ ReflectionFailed "Type error while constructing reflected error" e
                                       OK hs   -> return hs

                         -- Normalize error handler terms to produce the new messages
                         -- Need to use 'normaliseAll' since we have to reduce private
                         -- names in error handlers too
                         ctxt <- getContext
                         let results = map (normaliseAll ctxt []) (map fst handlers)
                         logElab 3 $ "New error message info: " ++ concat (intersperse " and " (map show results))

                         -- For each handler term output, either discard it if it is Nothing or reify it the Haskell equivalent
                         let errorpartsTT = mapMaybe unList (mapMaybe fromTTMaybe results)
                         errorparts <- case mapM (mapM reifyReportPart) errorpartsTT of
                                         Left err -> ierror err
                                         Right ok -> return ok
                         return $ case errorparts of
                                    []    -> e
                                    parts -> ReflectionError errorparts e

solveAll = try (do solve; solveAll) (return ())

-- | Do the left-over work after creating declarations in reflected
-- elaborator scripts
processTacticDecls :: ElabInfo -> [RDeclInstructions] -> Idris ()
processTacticDecls info steps =
  -- The order of steps is important: type declarations might
  -- establish metavars that later function bodies resolve.
  forM_ (reverse steps) $ \case
    RTyDeclInstrs n fc impls ty ->
      do logElab 3 $ "Declaration from tactics: " ++ show n ++ " : " ++ show ty
         logElab 3 $ "  It has impls " ++ show impls
         updateIState $ \i -> i { idris_implicits =
                                    addDef n impls (idris_implicits i) }
         addIBC (IBCImp n)
         ds <- checkDef info fc (\_ e -> e) True [(n, (-1, Nothing, ty, []))]
         addIBC (IBCDef n)
         ctxt <- getContext
         case lookupDef n ctxt of
           (TyDecl _ _ : _) ->
             -- If the function isn't defined at the end of the elab script,
             -- then it must be added as a metavariable. This needs guarding
             -- to prevent overwriting case defs with a metavar, if the case
             -- defs come after the type decl in the same script!
             let ds' = map (\(n, (i, top, t, ns)) -> (n, (i, top, t, ns, True, True))) ds
             in addDeferred ds'
           _ -> return ()
    RDatatypeDeclInstrs n impls ->
      do addIBC (IBCDef n)
         updateIState $ \i -> i { idris_implicits = addDef n impls (idris_implicits i) }
         addIBC (IBCImp n)

    RDatatypeDefnInstrs tyn tyconTy ctors ->
      do let cn (n, _, _) = n
             cimpls (_, impls, _) = impls
             cty (_, _, t) = t
         addIBC (IBCDef tyn)
         mapM_ (addIBC . IBCDef . cn) ctors
         ctxt <- getContext
         let params = findParams tyn (normalise ctxt [] tyconTy) (map cty ctors)
         let typeInfo = TI (map cn ctors) False [] params [] False
         -- implicit precondition to IBCData is that idris_datatypes on the IState is populated.
         -- otherwise writing the IBC just fails silently!
         updateIState $ \i -> i { idris_datatypes =
                                    addDef tyn typeInfo (idris_datatypes i) }
         addIBC (IBCData tyn)


         ttag <- getName -- from AbsSyntax.hs, really returns a disambiguating Int

         let metainf = DataMI params
         addIBC (IBCMetaInformation tyn metainf)
         updateContext (setMetaInformation tyn metainf)

         for_ ctors $ \(cn, impls, _) ->
           do updateIState $ \i -> i { idris_implicits = addDef cn impls (idris_implicits i) }
              addIBC (IBCImp cn)

         for_ ctors $ \(ctorN, _, _) ->
           do totcheck (NoFC, ctorN)
              ctxt <- tt_ctxt <$> getIState
              case lookupTyExact ctorN ctxt of
                Just cty -> do checkPositive (tyn : map cn ctors) (ctorN, cty)
                               return ()
                Nothing -> return ()

         case ctors of
            [ctor] -> do setDetaggable (cn ctor); setDetaggable tyn
                         addIBC (IBCOpt (cn ctor)); addIBC (IBCOpt tyn)
            _ -> return ()
         -- TODO: inaccessible

    RAddImplementation interfaceName implName ->
      do -- The interface resolution machinery relies on a special
         logElab 2 $ "Adding elab script implementation " ++ show implName ++
                     " for " ++ show interfaceName
         addImplementation False True interfaceName implName
         addIBC (IBCImplementation False True interfaceName implName)
    RClausesInstrs n cs ->
      do logElab 3 $ "Pattern-matching definition from tactics: " ++ show n
         solveDeferred emptyFC n
         let lhss = map (\(ns, lhs, _) -> (map fst ns, lhs)) cs
         let fc = fileFC "elab_reflected"
         pmissing <-
           do ist <- getIState
              possible <- genClauses fc n lhss
                                     (map (\ (ns, lhs) ->
                                        delab' ist lhs True True) lhss)
              missing <- filterM (checkPossible n) possible
              let undef = filter (noMatch ist (map snd lhss)) missing
              return undef
         let tot = if null pmissing
                      then Unchecked -- still need to check recursive calls
                      else Partial NotCovering -- missing cases implies not total
         setTotality n tot
         updateIState $ \i -> i { idris_patdefs =
                                    addDef n (cs, pmissing) $ idris_patdefs i }
         addIBC (IBCDef n)

         ctxt <- getContext
         case lookupDefExact n ctxt of
           Just (CaseOp _ _ _ _ _ cd) ->
             -- Here, we populate the call graph with a list of things
             -- we refer to, so that if they aren't total, the whole
             -- thing won't be.
             let (scargs, sc) = cases_compiletime cd
                 calls = map fst $ findCalls sc scargs
             in do logElab 2 $ "Called names in reflected elab: " ++ show calls
                   addCalls n calls
                   addIBC $ IBCCG n
           Just _ -> return () -- TODO throw internal error
           Nothing -> return ()

         -- checkDeclTotality requires that the call graph be present
         -- before calling it.
         -- TODO: reduce code duplication with Idris.Elab.Clause
         buildSCG (fc, n)

         -- Actually run the totality checker. In the main clause
         -- elaborator, this is deferred until after. Here, we run it
         -- now to get totality information as early as possible.
         tot' <- checkDeclTotality (fc, n)
         setTotality n tot'
         when (tot' /= Unchecked) $ addIBC (IBCTotal n tot')
  where
    -- TODO: see if the code duplication with Idris.Elab.Clause can be
    -- reduced or eliminated.
    -- These are always cases generated by genClauses
    checkPossible :: Name -> PTerm -> Idris Bool
    checkPossible fname lhs_in =
       do ctxt <- getContext
          ist <- getIState
          let lhs = addImplPat ist lhs_in
          let fc = fileFC "elab_reflected_totality"
          case elaborate (constraintNS info) ctxt (idris_datatypes ist) (idris_name ist) (sMN 0 "refPatLHS") infP initEState
                (erun fc (buildTC ist info EImpossible [] fname (allNamesIn lhs_in)
                                                                (infTerm lhs))) of
            OK (ElabResult lhs' _ _ _ _ _ name', _) ->
              do -- not recursively calling here, because we don't
                 -- want to run infinitely many times
                 let lhs_tm = orderPats (getInferTerm lhs')
                 updateIState $ \i -> i { idris_name = name' }
                 case recheck (constraintNS info) ctxt [] (forget lhs_tm) lhs_tm of
                      OK _ -> return True
                      err -> return False
            -- if it's a recoverable error, the case may become possible
            Error err -> return (recoverableCoverage ctxt err)


    -- TODO: Attempt to reduce/eliminate code duplication with Idris.Elab.Clause
    noMatch i cs tm = all (\x -> case matchClause i (delab' i x True True) tm of
                                   Right _ -> False
                                   Left  _ -> True) cs

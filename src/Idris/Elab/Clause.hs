{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Clause where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.DSL
import Idris.Error
import Idris.Delaborate
import Idris.Imports
import Idris.Elab.Term
import Idris.Coverage
import Idris.DataOpts
import Idris.Providers
import Idris.Primitives
import Idris.Inliner
import Idris.PartialEval
import Idris.Transforms
import Idris.DeepSeq
import Idris.Output (iputStrLn, pshow, iWarn, iRenderResult, sendHighlighting)
import IRTS.Lang

import Idris.Elab.AsPat
import Idris.Elab.Type
import Idris.Elab.Transform
import Idris.Elab.Utils

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.Typecheck
import Idris.Core.CaseTree

import Idris.Docstrings hiding (Unchecked)
import Util.Pretty hiding ((<$>))

import Prelude hiding (id, (.))
import Control.Category

import Control.Applicative hiding (Const)
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict as State
import qualified Control.Monad.State.Lazy as LState
import Data.List
import Data.Maybe
import Debug.Trace

import qualified Data.Map as Map
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Char(isLetter, toLower)
import Data.List.Split (splitOn)

import Util.Pretty(pretty, text)
import Numeric

-- | Elaborate a collection of left-hand and right-hand pairs - that is, a
-- top-level definition.
elabClauses :: ElabInfo -> FC -> FnOpts -> Name -> [PClause] -> Idris ()
elabClauses info' fc opts n_in cs =
      do let n    = liftname info n_in
             info = info' { elabFC = Just fc }
         ctxt <- getContext
         ist  <- getIState
         optimise <- getOptimise
         let petrans = PETransform `elem` optimise
         inacc <- map fst <$> fgetState (opt_inaccessible . ist_optimisation n)

         -- Check n actually exists, with no definition yet
         let tys = lookupTy n ctxt
         let reflect = Reflection `elem` opts
         checkUndefined n ctxt
         unless (length tys > 1) $ do
           fty <- case tys of
              [] -> -- TODO: turn into a CAF if there's no arguments
                    -- question: CAFs in where blocks?
                    tclift $ tfail $ At fc (NoTypeDecl n)
              [ty] -> return ty
           let atys = map snd (getArgTys fty)
           cs_elab <- mapM (elabClause info opts)
                           (zip [0..] cs)
           ctxt <- getContext
           -- pats_raw is the version we'll work with at compile time:
           -- no simplification or PE
           let (pats_in, cs_full) = unzip cs_elab
           let pats_raw = map (simple_lhs ctxt) pats_in
           logElab 3 $ "Elaborated patterns:\n" ++ show pats_raw

           solveDeferred fc n

           -- just ensure that the structure exists
           fmodifyState (ist_optimisation n) id
           addIBC (IBCOpt n)

           ist <- getIState
           ctxt <- getContext
           -- Don't apply rules if this is a partial evaluation definition,
           -- or we'll make something that just runs itself!
           let tpats = case specNames opts of
                            Nothing -> transformPats ist pats_in
                            _ -> pats_in

           -- If the definition is specialisable, this reduces the
           -- RHS
           pe_tm <- doPartialEval ist tpats
           let pats_pe = if petrans
                            then map (simple_lhs ctxt) pe_tm
                            else pats_raw

           let tcase = opt_typecase (idris_options ist)

           -- Look for 'static' names and generate new specialised
           -- definitions for them, as well as generating rewrite rules
           -- for partially evaluated definitions
           newrules <- if petrans
                          then mapM (\ e -> case e of
                                            Left _ -> return []
                                            Right (l, r) -> elabPE info fc n r) pats_pe
                          else return []

           -- Redo transforms with the newly generated transformations, so
           -- that the specialised application we've just made gets
           -- used in place of the general one
           ist <- getIState
           let pats_transformed = if petrans
                                     then transformPats ist pats_pe
                                     else pats_pe

           -- Summary of what's about to happen: Definitions go:
           --
           -- pats_in -> pats -> pdef -> pdef'

           -- addCaseDef builds case trees from <pdef> and <pdef'>

           -- pdef is the compile-time pattern definition.
           -- This will get further inlined to help with totality checking.
           let pdef = map (\(ns, lhs, rhs) -> (map fst ns, lhs, rhs)) $ map debind pats_raw
           -- pdef_pe is the one which will get further optimised
           -- for run-time, and, partially evaluated
           let pdef_pe = map debind pats_transformed

           logElab 5 $ "Initial typechecked patterns:\n" ++ show pats_raw
           logElab 5 $ "Initial typechecked pattern def:\n" ++ show pdef

           -- NOTE: Need to store original definition so that proofs which
           -- rely on its structure aren't affected by any changes to the
           -- inliner. Just use the inlined version to generate pdef' and to
           -- help with later inlinings.

           ist <- getIState
           let pdef_inl = inlineDef ist pdef

           numArgs <- tclift $ sameLength pdef

           case specNames opts of
                Just _ ->
                   do logElab 3 $ "Partially evaluated:\n" ++ show pats_pe
                _ -> return ()
           logElab 3 $ "Transformed:\n" ++ show pats_transformed

           erInfo <- getErasureInfo <$> getIState
           tree@(CaseDef scargs sc _) <- tclift $
                 simpleCase tcase (UnmatchedCase "Error") reflect CompileTime fc inacc atys pdef erInfo
           cov <- coverage
           pmissing <-
                   if cov && not (hasDefault pats_raw)
                      then do -- Generate clauses from the given possible cases
                              missing <- genClauses fc n (map getLHS pdef) cs_full
                              -- missing <- genMissing n scargs sc
                              missing' <- filterM (checkPossible info fc True n) missing
                              -- Filter out the ones which match one of the
                              -- given cases (including impossible ones)
                              let clhs = map getLHS pdef
                              logElab 2 $ "Must be unreachable:\n" ++
                                          showSep "\n" (map showTmImpls missing') ++
                                         "\nAgainst: " ++
                                          showSep "\n" (map (\t -> showTmImpls (delab ist t)) (map getLHS pdef))
                              -- filter out anything in missing' which is
                              -- matched by any of clhs. This might happen since
                              -- unification may force a variable to take a
                              -- particular form, rather than force a case
                              -- to be impossible.
                              return (filter (noMatch ist clhs) missing')
                      else return []
           let pcover = null pmissing

           -- pdef' is the version that gets compiled for run-time,
           -- so we start from the partially evaluated version
           pdef_in' <- applyOpts $ map (\(ns, lhs, rhs) -> (map fst ns, lhs, rhs)) pdef_pe
           ctxt <- getContext
           let pdef' = map (simple_rt ctxt) pdef_in'

           logElab 5 $ "After data structure transformations:\n" ++ show pdef'

           ist <- getIState
  --          let wf = wellFounded ist n sc
           let tot | pcover || AssertTotal `elem` opts = Unchecked -- finish later
                   | PEGenerated `elem` opts = Generated
                   | otherwise = Partial NotCovering -- already know it's not total

  --          case lookupCtxt (namespace info) n (idris_flags ist) of
  --             [fs] -> if TotalFn `elem` fs
  --                       then case tot of
  --                               Total _ -> return ()
  --                               t -> tclift $ tfail (At fc (Msg (show n ++ " is " ++ show t)))
  --             _ -> return ()
           case tree of
               CaseDef _ _ [] -> return ()
               CaseDef _ _ xs -> mapM_ (\x ->
                   iputStrLn $ show fc ++
                                ":warning - Unreachable case: " ++
                                   show (delab ist x)) xs
           let knowncovering = (pcover && cov) || AssertTotal `elem` opts
           let defaultcase = if knowncovering
                                then STerm Erased
                                else UnmatchedCase $ "*** " ++
                                      show fc ++
                                       ":unmatched case in " ++ show n ++
                                       " ***"

           tree' <- tclift $ simpleCase tcase defaultcase reflect
                                        RunTime fc inacc atys pdef' erInfo
           logElab 3 $ "Unoptimised " ++ show n ++ ": " ++ show tree
           logElab 3 $ "Optimised: " ++ show tree'
           ctxt <- getContext
           ist <- getIState
           let opt = idris_optimisation ist
           putIState (ist { idris_patdefs = addDef n (force pdef_pe, force pmissing)
                                                (idris_patdefs ist) })
           let caseInfo = CaseInfo (inlinable opts) (inlinable opts) (dictionary opts)
           case lookupTyExact n ctxt of
               Just ty ->
                   do ctxt' <- do ctxt <- getContext
                                  tclift $
                                    addCasedef n erInfo caseInfo
                                                   tcase defaultcase
                                                   reflect
                                                   (AssertTotal `elem` opts)
                                                   atys
                                                   inacc
                                                   pats_pe
                                                   pdef
                                                   pdef -- compile time
                                                   pdef_inl -- inlined
                                                   pdef' ty
                                                   ctxt
                      setContext ctxt'
                      addIBC (IBCDef n)
                      addDefinedName n
                      setTotality n tot
                      when (not reflect && PEGenerated `notElem` opts) $
                                           do totcheck (fc, n)
                                              defer_totcheck (fc, n)
                      when (tot /= Unchecked) $ addIBC (IBCTotal n tot)
                      i <- getIState
                      ctxt <- getContext
                      case lookupDef n ctxt of
                          (CaseOp _ _ _ _ _ cd : _) ->
                            let (scargs, sc) = cases_compiletime cd in
                              do let calls = map fst $ findCalls sc scargs
                                 -- let scg = buildSCG i sc scargs
                                 -- add SCG later, when checking totality
                                 logElab 2 $ "Called names: " ++ show calls
                                 -- if the definition is public, make sure
                                 -- it only uses public names
                                 nvis <- getFromHideList n
                                 case nvis of
                                      Just Public -> mapM_ (checkVisibility fc n Public Public) calls
                                      _ -> return ()
                                 addCalls n calls
                                 addIBC (IBCCG n)
                          _ -> return ()
                      return ()
  --                         addIBC (IBCTotal n tot)
               _ -> return ()
           -- Check it's covering, if 'covering' option is used. Chase
           -- all called functions, and fail if any of them are also
           -- 'Partial NotCovering'
           when (CoveringFn `elem` opts) $ checkAllCovering fc [] n n
  where
    noMatch i cs tm = all (\x -> case trim_matchClause i (delab' i x True True) tm of
                                      Right _ -> False
                                      Left miss -> True) cs
      where
        trim_matchClause i (PApp fcl fl ls) (PApp fcr fr rs)
            = let args = min (length ls) (length rs) in
                  matchClause i (PApp fcl fl (take args ls))
                                (PApp fcr fr (take args rs))

    checkUndefined n ctxt = case lookupDef n ctxt of
                                 [] -> return ()
                                 [TyDecl _ _] -> return ()
                                 _ -> tclift $ tfail (At fc (AlreadyDefined n))

    debind (Right (x, y)) = let (vs, x') = depat [] x
                                (_, y') = depat [] y in
                                (vs, x', y')
    debind (Left x)       = let (vs, x') = depat [] x in
                                (vs, x', Impossible)

    depat acc (Bind n (PVar t) sc) = depat ((n, t) : acc) (instantiate (P Bound n t) sc)
    depat acc x = (acc, x)


    getPVs (Bind x (PVar _) tm) = let (vs, tm') = getPVs tm
                                  in (x:vs, tm')
    getPVs tm = ([], tm)

    isPatVar vs (P Bound n _) = n `elem` vs
    isPatVar _ _ = False

    hasDefault cs | (Right (lhs, rhs) : _) <- reverse cs
                  , (pvs, tm) <- getPVs (explicitNames lhs)
                  , (f, args) <- unApply tm = all (isPatVar pvs) args
    hasDefault _ = False

    getLHS (_, l, _) = l

    -- Simplify the left hand side of a definition, to remove any lets
    -- that may have arisen during elaboration
    simple_lhs ctxt (Right (x, y)) = Right (Idris.Core.Evaluate.simplify ctxt [] x, y)
    simple_lhs ctxt t = t

    simple_rt ctxt (p, x, y) = (p, x, force (uniqueBinders p
                                                (rt_simplify ctxt [] y)))

    specNames [] = Nothing
    specNames (Specialise ns : _) = Just ns
    specNames (_ : xs) = specNames xs

    sameLength ((_, x, _) : xs)
        = do l <- sameLength xs
             let (f, as) = unApply x
             if (null xs || l == length as) then return (length as)
                else tfail (At fc (Msg "Clauses have differing numbers of arguments "))
    sameLength [] = return 0

    -- Partially evaluate, if the definition is marked as specialisable
    doPartialEval ist pats =
           case specNames opts of
                Nothing -> return pats
                Just ns -> case partial_eval (tt_ctxt ist) ns pats of
                                Just t -> return t
                                Nothing -> ierror (At fc (Msg "No specialisation achieved"))

-- | Find 'static' applications in a term and partially evaluate them.
-- Return any new transformation rules
elabPE :: ElabInfo -> FC -> Name -> Term -> Idris [(Term, Term)]
elabPE info fc caller r =
  do ist <- getIState
     let sa = filter (\ap -> fst ap /= caller) $ getSpecApps ist [] r
     rules <- mapM mkSpecialised sa
     return $ concat rules
  where
    -- Make a specialised version of the application, and
    -- add a PTerm level transformation rule, which is basically the
    -- new definition in reverse (before specialising it).
    -- RHS => LHS where implicit arguments are left blank in the
    -- transformation.

    -- Transformation rules are applied after every PClause elaboration

    mkSpecialised :: (Name, [(PEArgType, Term)]) -> Idris [(Term, Term)]
    mkSpecialised specapp_in = do
        ist <- getIState
        ctxt <- getContext
        let (specTy, specapp) = getSpecTy ist specapp_in
        let (n, newnm, specdecl) = getSpecClause ist specapp
        let lhs = pe_app specdecl
        let rhs = pe_def specdecl
        let undef = case lookupDefExact newnm ctxt of
                         Nothing -> True
                         _ -> False
        logElab 5 $ show (newnm, undef, map (concreteArg ist) (snd specapp))
        idrisCatch
          (if (undef && all (concreteArg ist) (snd specapp)) then do
                cgns <- getAllNames n
                -- on the RHS of the new definition, we should reduce
                -- everything that's not itself static (because we'll
                -- want to be a PE version of those next)
                let cgns' = filter (\x -> x /= n &&
                                          notStatic ist x) cgns
                -- set small reduction limit on partial/productive things
                let maxred = case lookupTotal n ctxt of
                                  [Total _] -> 65536
                                  [Productive] -> 16
                                  _ -> 1
                let opts = [Specialise ((if pe_simple specdecl
                                            then map (\x -> (x, Nothing)) cgns'
                                            else []) ++
                                         (n, Just maxred) :
                                           mapMaybe (specName (pe_simple specdecl))
                                                    (snd specapp))]
                logElab 3 $ "Specialising application: " ++ show specapp
                              ++ " in " ++ show caller ++
                              " with " ++ show opts
                logElab 3 $ "New name: " ++ show newnm
                logElab 3 $ "PE definition type : " ++ (show specTy)
                            ++ "\n" ++ show opts
                logElab 3 $ "PE definition " ++ show newnm ++ ":\n" ++
                             showSep "\n"
                                (map (\ (lhs, rhs) ->
                                  (showTmImpls lhs ++ " = " ++
                                   showTmImpls rhs)) (pe_clauses specdecl))

                logElab 2 $ show n ++ " transformation rule: " ++
                           showTmImpls rhs ++ " ==> " ++ showTmImpls lhs

                elabType info defaultSyntax emptyDocstring [] fc opts newnm NoFC specTy
                let def = map (\(lhs, rhs) ->
                                 let lhs' = mapPT hiddenToPH $ stripUnmatchable ist lhs in
                                  PClause fc newnm lhs' [] rhs [])
                              (pe_clauses specdecl)
                trans <- elabTransform info fc False rhs lhs
                elabClauses info fc (PEGenerated:opts) newnm def
                return [trans]
             else return [])
          -- if it doesn't work, just don't specialise. Could happen for lots
          -- of valid reasons (e.g. local variables in scope which can't be
          -- lifted out).
          (\e -> do logElab 3 $ "Couldn't specialise: " ++ (pshow ist e)
                    return [])

    hiddenToPH (PHidden _) = Placeholder
    hiddenToPH x = x

    specName simpl (ImplicitS, tm)
        | (P Ref n _, _) <- unApply tm = Just (n, Just (if simpl then 1 else 0))
    specName simpl (ExplicitS, tm)
        | (P Ref n _, _) <- unApply tm = Just (n, Just (if simpl then 1 else 0))
    specName simpl _ = Nothing

    notStatic ist n = case lookupCtxtExact n (idris_statics ist) of
                           Just s -> not (or s)
                           _ -> True

    concreteArg ist (ImplicitS, tm) = concreteTm ist tm
    concreteArg ist (ExplicitS, tm) = concreteTm ist tm
    concreteArg ist _ = True

    concreteTm ist tm | (P _ n _, _) <- unApply tm =
        case lookupTy n (tt_ctxt ist) of
             [] -> False
             _ -> True
    concreteTm ist (Constant _) = True
    concreteTm ist (Bind n (Lam _) sc) = True
    concreteTm ist (Bind n (Pi _ _ _) sc) = True
    concreteTm ist (Bind n (Let _ _) sc) = concreteTm ist sc
    concreteTm ist _ = False

    -- get the type of a specialised application
    getSpecTy ist (n, args)
       = case lookupTy n (tt_ctxt ist) of
              [ty] -> let (specty_in, args') = specType args (explicitNames ty)
                          specty = normalise (tt_ctxt ist) [] (finalise specty_in)
                          t = mkPE_TyDecl ist args' (explicitNames specty) in
                          (t, (n, args'))
--                             (normalise (tt_ctxt ist) [] (specType args ty))
              _ -> error "Can't happen (getSpecTy)"

    -- get the clause of a specialised application
    getSpecClause ist (n, args)
       = let newnm = sUN ("PE_" ++ show (nsroot n) ++ "_" ++
                               qhash 5381 (showSep "_" (map showArg args))) in
                               -- UN (show n ++ show (map snd args)) in
             (n, newnm, mkPE_TermDecl ist newnm n args)
      where showArg (ExplicitS, n) = qshow n
            showArg (ImplicitS, n) = qshow n
            showArg _ = ""

            qshow (Bind _ _ _) = "fn"
            qshow (App _ f a) = qshow f ++ qshow a
            qshow (P _ n _) = show n
            qshow (Constant c) = show c
            qshow _ = ""

            -- Simple but effective string hashing...
            -- Keep it to 32 bits for readability/debuggability
            qhash :: Int -> String -> String
            qhash hash [] = showHex (abs hash `mod` 0xffffffff) ""
            qhash hash (x:xs) = qhash (hash * 33 + fromEnum x) xs

-- | Checks if the clause is a possible left hand side.
checkPossible :: ElabInfo -> FC -> Bool -> Name -> PTerm -> Idris Bool
checkPossible info fc tcgen fname lhs_in
   = do ctxt <- getContext
        i <- getIState
        let lhs = addImplPat i lhs_in
        -- if the LHS type checks, it is possible
        case elaborate ctxt (idris_datatypes i) (idris_name i) (sMN 0 "patLHS") infP initEState
                            (erun fc (buildTC i info ELHS [] fname
                                                (allNamesIn lhs_in)
                                                (infTerm lhs))) of
            OK (ElabResult lhs' _ _ ctxt' newDecls highlights newGName, _) ->
               do setContext ctxt'
                  processTacticDecls info newDecls
                  sendHighlighting highlights
                  updateIState $ \i -> i { idris_name = newGName }
                  let lhs_tm = orderPats (getInferTerm lhs')
                  case recheck ctxt' [] (forget lhs_tm) lhs_tm of
                       OK _ -> return True
                       err -> return False
            -- if it's a recoverable error, the case may become possible
            Error err -> if tcgen then return (recoverableCoverage ctxt err)
                                  else return (validCoverageCase ctxt err ||
                                                 recoverableCoverage ctxt err)


propagateParams :: IState -> [Name] -> Type -> [Name] -> PTerm -> PTerm
propagateParams i ps t bound tm@(PApp _ (PRef fc hls n) args)
     = PApp fc (PRef fc hls n) (addP t args)
   where addP (Bind n _ sc) (t : ts)
              | Placeholder <- getTm t,
                n `elem` ps,
                not (n `elem` bound)
                    = t { getTm = PPatvar NoFC n } : addP sc ts
         addP (Bind n _ sc) (t : ts) = t : addP sc ts
         addP _ ts = ts
propagateParams i ps t bound (PApp fc ap args)
     = PApp fc (propagateParams i ps t bound ap) args
propagateParams i ps t bound (PRef fc hls n)
     = case lookupCtxt n (idris_implicits i) of
            [is] -> let ps' = filter (isImplicit is) ps in
                        PApp fc (PRef fc hls n) (map (\x -> pimp x (PRef fc [] x) True) ps')
            _ -> PRef fc hls n
    where isImplicit [] n = False
          isImplicit (PImp _ _ _ x _ : is) n | x == n = True
          isImplicit (_ : is) n = isImplicit is n
propagateParams i ps t bound x = x

findUnique :: Context -> Env -> Term -> [Name]
findUnique ctxt env (Bind n b sc)
   = let rawTy = forgetEnv (map fst env) (binderTy b)
         uniq = case check ctxt env rawTy of
                     OK (_, UType UniqueType) -> True
                     OK (_, UType NullType) -> True
                     OK (_, UType AllTypes) -> True
                     _ -> False in
         if uniq then n : findUnique ctxt ((n, b) : env) sc
                 else findUnique ctxt ((n, b) : env) sc
findUnique _ _ _ = []

-- Return the elaborated LHS/RHS, and the original LHS with implicits added
elabClause :: ElabInfo -> FnOpts -> (Int, PClause) ->
              Idris (Either Term (Term, Term), PTerm)
elabClause info opts (_, PClause fc fname lhs_in [] PImpossible [])
   = do let tcgen = Dictionary `elem` opts
        i <- get
        let lhs = addImpl [] i lhs_in
        b <- checkPossible info fc tcgen fname lhs_in
        case b of
            True -> tclift $ tfail (At fc
                                (Msg $ show lhs_in ++ " is a valid case"))
            False -> do ptm <- mkPatTm lhs_in
                        return (Left ptm, lhs)
elabClause info opts (cnum, PClause fc fname lhs_in_as withs rhs_in_as whereblock)
   = do let tcgen = Dictionary `elem` opts
        push_estack fname False
        ctxt <- getContext
        let (lhs_in, rhs_in) = desugarAs lhs_in_as rhs_in_as

        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        i <- getIState
        inf <- isTyInferred fname

        -- Check if we have "with" patterns outside of "with" block
        when (isOutsideWith lhs_in && (not $ null withs)) $
            ierror $ (At fc (Elaborating "left hand side of " fname Nothing
                             (Msg "unexpected patterns outside of \"with\" block")))

        -- get the parameters first, to pass through to any where block
        let fn_ty = case lookupTy fname ctxt of
                         [t] -> t
                         _ -> error "Can't happen (elabClause function type)"
        let fn_is = case lookupCtxt fname (idris_implicits i) of
                         [t] -> t
                         _ -> []
        let norm_ty = normalise ctxt [] fn_ty
        let params = getParamsInType i [] fn_is norm_ty
        let tcparams = getTCParamsInType i [] fn_is norm_ty

        let lhs = mkLHSapp $ stripLinear i $ stripUnmatchable i $
                    propagateParams i params norm_ty (allNamesIn lhs_in) (addImplPat i lhs_in)
--         let lhs = mkLHSapp $
--                     propagateParams i params fn_ty (addImplPat i lhs_in)
        logElab 10 (show (params, fn_ty) ++ " " ++ showTmImpls (addImplPat i lhs_in))
        logElab 5 ("LHS: " ++ show opts ++ "\n" ++ show fc ++ " " ++ showTmImpls lhs)
        logElab 4 ("Fixed parameters: " ++ show params ++ " from " ++ showTmImpls lhs_in ++
                  "\n" ++ show (fn_ty, fn_is))

        ((ElabResult lhs' dlhs [] ctxt' newDecls highlights newGName, probs, inj), _) <-
           tclift $ elaborate ctxt (idris_datatypes i) (idris_name i) (sMN 0 "patLHS") infP initEState
                    (do res <- errAt "left hand side of " fname Nothing
                                 (erun fc (buildTC i info ELHS opts fname
                                          (allNamesIn lhs_in)
                                          (infTerm lhs)))
                        probs <- get_probs
                        inj <- get_inj
                        return (res, probs, inj))
        setContext ctxt'
        processTacticDecls info newDecls
        sendHighlighting highlights
        updateIState $ \i -> i { idris_name = newGName }

        when inf $ addTyInfConstraints fc (map (\(x,y,_,_,_,_,_) -> (x,y)) probs)

        let lhs_tm = orderPats (getInferTerm lhs')
        let lhs_ty = getInferType lhs'
        let static_names = getStaticNames i lhs_tm

        logElab 3 ("Elaborated: " ++ show lhs_tm)
        logElab 3 ("Elaborated type: " ++ show lhs_ty)
        logElab 5 ("Injective: " ++ show fname ++ " " ++ show inj)

        -- If we're inferring metavariables in the type, don't recheck,
        -- because we're only doing this to try to work out those metavariables
        ctxt <- getContext
        (clhs_c, clhsty) <- if not inf
                               then recheckC_borrowing False (PEGenerated `notElem` opts)
                                                       [] fc id [] lhs_tm
                               else return (lhs_tm, lhs_ty)
        let clhs = Idris.Core.Evaluate.simplify ctxt [] clhs_c
        let borrowed = borrowedNames [] clhs

        -- These are the names we're not allowed to use on the RHS, because
        -- they're UniqueTypes and borrowed from another function.
        -- FIXME: There is surely a nicer way than this...
        -- Issue #1615 on the Issue Tracker.
        --     https://github.com/idris-lang/Idris-dev/issues/1615
        when (not (null borrowed)) $
          logElab 5 ("Borrowed names on LHS: " ++ show borrowed)

        logElab 3 ("Normalised LHS: " ++ showTmImpls (delabMV i clhs))

        rep <- useREPL
        when rep $ do
          addInternalApp (fc_fname fc) (fst . fc_start $ fc) (delabMV i clhs) -- TODO: Should use span instead of line and filename?
        addIBC (IBCLineApp (fc_fname fc) (fst . fc_start $ fc) (delabMV i clhs))

        logElab 5 ("Checked " ++ show clhs ++ "\n" ++ show clhsty)
        -- Elaborate where block
        ist <- getIState
        ctxt <- getContext

        windex <- getName
        let decls = nub (concatMap declared whereblock)
        let defs = nub (decls ++ concatMap defined whereblock)
        let newargs_all = pvars ist lhs_tm

        -- Unique arguments must be passed to the where block explicitly
        -- (since we can't control "usage" easlily otherwise). Remove them
        -- from newargs here
        let uniqargs = findUnique ctxt [] lhs_tm
        let newargs = filter (\(n,_) -> n `notElem` uniqargs) newargs_all

        let winfo = (pinfo info newargs defs windex) { elabFC = Just fc }
        let wb = map (mkStatic static_names) $
                 map (expandParamsD False ist decorate newargs defs) whereblock

        -- Split the where block into declarations with a type, and those
        -- without
        -- Elaborate those with a type *before* RHS, those without *after*
        let (wbefore, wafter) = sepBlocks wb

        logElab 2 $ "Where block:\n " ++ show wbefore ++ "\n" ++ show wafter
        mapM_ (rec_elabDecl info EAll winfo) wbefore
        -- Now build the RHS, using the type of the LHS as the goal.
        i <- getIState -- new implicits from where block
        logElab 5 (showTmImpls (expandParams decorate newargs defs (defs \\ decls) rhs_in))
        let rhs = rhs_trans info $
                   addImplBoundInf i (map fst newargs_all) (defs \\ decls)
                                 (expandParams decorate newargs defs (defs \\ decls) rhs_in)
        logElab 2 $ "RHS: " ++ show (map fst newargs_all) ++ " " ++ showTmImpls rhs
        ctxt <- getContext -- new context with where block added
        logElab 5 "STARTING CHECK"
        ((rhs', defer, holes, is, probs, ctxt', newDecls, highlights, newGName), _) <-
           tclift $ elaborate ctxt (idris_datatypes i) (idris_name i) (sMN 0 "patRHS") clhsty initEState
                    (do pbinds ist lhs_tm
                        -- proof search can use explicitly written names
                        mapM_ addPSname (allNamesIn lhs_in)
                        mapM_ setinj (nub (tcparams ++ inj))
                        setNextName
                        (ElabResult _ _ is ctxt' newDecls highlights newGName) <-
                          errAt "right hand side of " fname (Just clhsty)
                                (erun fc (build i winfo ERHS opts fname rhs))
                        errAt "right hand side of " fname (Just clhsty)
                              (erun fc $ psolve lhs_tm)
                        tt <- get_term
                        aux <- getAux
                        let (tm, ds) = runState (collectDeferred (Just fname)
                                                     (map fst $ case_decls aux) ctxt tt) []
                        probs <- get_probs
                        hs <- get_holes
                        return (tm, ds, hs, is, probs, ctxt', newDecls, highlights, newGName))
        setContext ctxt'
        processTacticDecls info newDecls
        sendHighlighting highlights
        updateIState $ \i -> i { idris_name = newGName }

        when inf $ addTyInfConstraints fc (map (\(x,y,_,_,_,_,_) -> (x,y)) probs)

        logElab 5 "DONE CHECK"
        logElab 4 $ "---> " ++ show rhs'
        when (not (null defer)) $ logElab 1 $ "DEFERRED " ++
                    show (map (\ (n, (_,_,t,_)) -> (n, t)) defer)

        -- If there's holes, set the metavariables as undefinable
        def' <- checkDef fc (\n -> Elaborating "deferred type of " n Nothing) (null holes) defer
        let def'' = map (\(n, (i, top, t, ns)) -> (n, (i, top, t, ns, False, null holes))) def'
        addDeferred def''

        mapM_ (\(n, _) -> addIBC (IBCDef n)) def''

        when (not (null def')) $ do
           mapM_ defer_totcheck (map (\x -> (fc, fst x)) def'')

        -- Now the remaining deferred (i.e. no type declarations) clauses
        -- from the where block

        mapM_ (rec_elabDecl info EAll winfo) wafter
        mapM_ (elabCaseBlock winfo opts) is

        ctxt <- getContext
        logElab 5 $ "Rechecking"
        logElab 6 $ " ==> " ++ show (forget rhs')

        (crhs, crhsty) -- if there's holes && deferred things, it's okay
                       -- but we'll need to freeze the definition and not
                       -- allow the deferred things to be definable
                       -- (this is just to allow users to inspect intermediate
                       -- things)
             <- if (null holes || null def') && not inf 
                   then recheckC_borrowing True (PEGenerated `notElem` opts)
                                       borrowed fc id [] rhs'
                   else return (rhs', clhsty)

        logElab 6 $ " ==> " ++ showEnvDbg [] crhsty ++ "   against   " ++ showEnvDbg [] clhsty

        -- If there's holes, make sure this definition is frozen
        when (not (null holes)) $ do
           logElab 5 $ "Making " ++ show fname ++ " frozen due to " ++ show holes
           setAccessibility fname Frozen

        ctxt <- getContext
        let constv = next_tvar ctxt
        case LState.runStateT (convertsC ctxt [] crhsty clhsty) (constv, []) of
            OK (_, cs) -> when (PEGenerated `notElem` opts) $ do
                             addConstraints fc cs
                             logElab 6 $ "CONSTRAINTS ADDED: " ++ show cs ++ "\n" ++ show (clhsty, crhsty)
                             return ()
            Error e -> ierror (At fc (CantUnify False (clhsty, Nothing) (crhsty, Nothing) e [] 0))
        i <- getIState
        checkInferred fc (delab' i crhs True True) rhs
        -- if the function is declared '%error_reverse', or its type,
        -- then we'll try running it in reverse to improve error messages
        let (ret_fam, _) = unApply (getRetTy crhsty)
        rev <- case ret_fam of
                    P _ rfamn _ ->
                        case lookupCtxt rfamn (idris_datatypes i) of
                             [TI _ _ dopts _ _] ->
                                 return (DataErrRev `elem` dopts)
                             _ -> return False
                    _ -> return False

        when (rev || ErrorReverse `elem` opts) $ do
           addIBC (IBCErrRev (crhs, clhs))
           addErrRev (crhs, clhs)
        pop_estack
        return $ (Right (clhs, crhs), lhs)
  where
    pinfo :: ElabInfo -> [(Name, PTerm)] -> [Name] -> Int -> ElabInfo
    pinfo info ns ds i
          = let newps = params info ++ ns
                dsParams = map (\n -> (n, map fst newps)) ds
                newb = addAlist dsParams (inblock info)
                l = liftname info in
                info { params = newps,
                       inblock = newb,
                       liftname = id -- (\n -> case lookupCtxt n newb of
                                     --      Nothing -> n
                                     --      _ -> MN i (show n)) . l
                     }

    -- Find the variable names which appear under a 'Ownership.Read' so that
    -- we know they can't be used on the RHS
    borrowedNames :: [Name] -> Term -> [Name]
    borrowedNames env (App _ (App _ (P _ (NS (UN lend) [owner]) _) _) arg)
        | owner == txt "Ownership" &&
          (lend == txt "lend" || lend == txt "Read") = getVs arg
       where
         getVs (V i) = [env!!i]
         getVs (App _ f a) = nub $ getVs f ++ getVs a
         getVs _ = []
    borrowedNames env (App _ f a) = nub $ borrowedNames env f ++ borrowedNames env a
    borrowedNames env (Bind n b sc) = nub $ borrowedB b ++ borrowedNames (n:env) sc
       where borrowedB (Let t v) = nub $ borrowedNames env t ++ borrowedNames env v
             borrowedB b = borrowedNames env (binderTy b)
    borrowedNames _ _ = []

    mkLHSapp t@(PRef _ _ _) = PApp fc t []
    mkLHSapp t = t

    decorate (NS x ns)
       = NS (SN (WhereN cnum fname x)) ns -- ++ [show cnum])
--        = NS (UN ('#':show x)) (ns ++ [show cnum, show fname])
    decorate x
       = SN (WhereN cnum fname x)
--        = NS (SN (WhereN cnum fname x)) [show cnum]
--        = NS (UN ('#':show x)) [show cnum, show fname]

    sepBlocks bs = sepBlocks' [] bs where
      sepBlocks' ns (d@(PTy _ _ _ _ _ n _ t) : bs)
            = let (bf, af) = sepBlocks' (n : ns) bs in
                  (d : bf, af)
      sepBlocks' ns (d@(PClauses _ _ n _) : bs)
         | not (n `elem` ns) = let (bf, af) = sepBlocks' ns bs in
                                   (bf, d : af)
      sepBlocks' ns (b : bs) = let (bf, af) = sepBlocks' ns bs in
                                   (b : bf, af)
      sepBlocks' ns [] = ([], [])

    -- term is not within "with" block
    isOutsideWith :: PTerm -> Bool
    isOutsideWith (PApp _ (PRef _ _ (SN (WithN _ _))) _) = False
    isOutsideWith _ = True

elabClause info opts (_, PWith fc fname lhs_in withs wval_in pn_in withblock)
   = do let tcgen = Dictionary `elem` opts
        ctxt <- getContext
        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        i <- getIState
        -- get the parameters first, to pass through to any where block
        let fn_ty = case lookupTy fname ctxt of
                         [t] -> t
                         _ -> error "Can't happen (elabClause function type)"
        let fn_is = case lookupCtxt fname (idris_implicits i) of
                         [t] -> t
                         _ -> []
        let params = getParamsInType i [] fn_is (normalise ctxt [] fn_ty)
        let lhs = stripLinear i $ stripUnmatchable i $
                   propagateParams i params fn_ty (allNamesIn lhs_in)
                    (addImplPat i lhs_in)
        logElab 2 ("LHS: " ++ show lhs)
        (ElabResult lhs' dlhs [] ctxt' newDecls highlights newGName, _) <-
            tclift $ elaborate ctxt (idris_datatypes i) (idris_name i) (sMN 0 "patLHS") infP initEState
              (errAt "left hand side of with in " fname Nothing
                (erun fc (buildTC i info ELHS opts fname
                                  (allNamesIn lhs_in)
                                  (infTerm lhs))) )
        setContext ctxt'
        processTacticDecls info newDecls
        sendHighlighting highlights
        updateIState $ \i -> i { idris_name = newGName }

        ctxt <- getContext
        let lhs_tm = orderPats (getInferTerm lhs')
        let lhs_ty = getInferType lhs'
        let ret_ty = getRetTy (explicitNames (normalise ctxt [] lhs_ty))
        let static_names = getStaticNames i lhs_tm
        logElab 5 (show lhs_tm ++ "\n" ++ show static_names)
        (clhs, clhsty) <- recheckC fc id [] lhs_tm
        logElab 5 ("Checked " ++ show clhs)
        let bargs = getPBtys (explicitNames (normalise ctxt [] lhs_tm))
        let wval = rhs_trans info $ addImplBound i (map fst bargs) wval_in
        logElab 5 ("Checking " ++ showTmImpls wval)
        -- Elaborate wval in this context
        ((wval', defer, is, ctxt', newDecls, highlights, newGName), _) <-
            tclift $ elaborate ctxt (idris_datatypes i) (idris_name i) (sMN 0 "withRHS")
                        (bindTyArgs PVTy bargs infP) initEState
                        (do pbinds i lhs_tm
                            -- proof search can use explicitly written names
                            mapM_ addPSname (allNamesIn lhs_in)
                            setNextName
                            -- TODO: may want where here - see winfo abpve
                            (ElabResult _ d is ctxt' newDecls highlights newGName) <- errAt "with value in " fname Nothing
                              (erun fc (build i info ERHS opts fname (infTerm wval)))
                            erun fc $ psolve lhs_tm
                            tt <- get_term
                            return (tt, d, is, ctxt', newDecls, highlights, newGName))
        setContext ctxt'
        processTacticDecls info newDecls
        sendHighlighting highlights
        updateIState $ \i -> i { idris_name = newGName }

        def' <- checkDef fc iderr True defer
        let def'' = map (\(n, (i, top, t, ns)) -> (n, (i, top, t, ns, False, True))) def'
        addDeferred def''
        mapM_ (elabCaseBlock info opts) is
        logElab 5 ("Checked wval " ++ show wval')

        ctxt <- getContext
        (cwval, cwvalty) <- recheckC fc id [] (getInferTerm wval')
        let cwvaltyN = explicitNames (normalise ctxt [] cwvalty)
        let cwvalN = explicitNames (normalise ctxt [] cwval)
        logElab 3 ("With type " ++ show cwvalty ++ "\nRet type " ++ show ret_ty)
        -- We're going to assume the with type is not a function shortly,
        -- so report an error if it is (you can't match on a function anyway
        -- so this doesn't lose anything)
        case getArgTys cwvaltyN of
             [] -> return ()
             (_:_) -> ierror $ At fc (WithFnType cwvalty)

        let pvars = map fst (getPBtys cwvalty)
        -- we need the unelaborated term to get the names it depends on
        -- rather than a de Bruijn index.
        let pdeps = usedNamesIn pvars i (delab i cwvalty)
        let (bargs_pre, bargs_post) = split pdeps bargs []

        let mpn = case pn_in of
                       Nothing -> Nothing
                       Just (n, nfc) -> Just (uniqueName n (map fst bargs))

        -- Highlight explicit proofs
        sendHighlighting $ [(fc, AnnBoundName n False) | (n, fc) <- maybeToList pn_in]

        logElab 10 ("With type " ++ show (getRetTy cwvaltyN) ++
                  " depends on " ++ show pdeps ++ " from " ++ show pvars)
        logElab 10 ("Pre " ++ show bargs_pre ++ "\nPost " ++ show bargs_post)
        windex <- getName
        -- build a type declaration for the new function:
        -- (ps : Xs) -> (withval : cwvalty) -> (ps' : Xs') -> ret_ty
        let wargval = getRetTy cwvalN
        let wargtype = getRetTy cwvaltyN
        let wargname = sMN windex "warg"

        logElab 5 ("Abstract over " ++ show wargval ++ " in " ++ show wargtype)
        let wtype = bindTyArgs (flip (Pi Nothing) (TType (UVar 0))) (bargs_pre ++
                     (wargname, wargtype) :
                     map (abstract wargname wargval wargtype) bargs_post ++
                     case mpn of
                          Just pn -> [(pn, mkApp (P Ref eqTy Erased)
                                       [wargtype, wargtype,
                                         P Bound wargname Erased, wargval])]
                          Nothing -> [])
                     (substTerm wargval (P Bound wargname wargtype) ret_ty)
        logElab 3 ("New function type " ++ show wtype)
        let wname = SN (WithN windex fname)

        let imps = getImps wtype -- add to implicits context
        putIState (i { idris_implicits = addDef wname imps (idris_implicits i) })
        let statics = getStatics static_names wtype
        logElab 5 ("Static positions " ++ show statics)
        i <- getIState
        putIState (i { idris_statics = addDef wname statics (idris_statics i) })

        addIBC (IBCDef wname)
        addIBC (IBCImp wname)
        addIBC (IBCStatic wname)

        def' <- checkDef fc iderr True [(wname, (-1, Nothing, wtype, []))]
        let def'' = map (\(n, (i, top, t, ns)) -> (n, (i, top, t, ns, False, True))) def'
        addDeferred def''

        -- in the subdecls, lhs becomes:
        --         fname  pats | wpat [rest]
        --    ==>  fname' ps   wpat [rest], match pats against toplevel for ps
        wb <- mapM (mkAuxC mpn wname lhs (map fst bargs_pre) (map fst bargs_post))
                       withblock
        logElab 3 ("with block " ++ show wb)
        -- propagate totality assertion to the new definitions
        setFlags wname [Inlinable]
        when (AssertTotal `elem` opts) $ setFlags wname [Inlinable, AssertTotal]
        i <- getIState
        let rhstrans' = updateWithTerm i mpn wname lhs (map fst bargs_pre) (map fst (bargs_post))
                             . rhs_trans info
        mapM_ (rec_elabDecl info EAll (info { rhs_trans = rhstrans' })) wb

        -- rhs becomes: fname' ps_pre wval ps_post Refl
        let rhs = PApp fc (PRef fc [] wname)
                    (map (pexp . (PRef fc []) . fst) bargs_pre ++
                        pexp wval :
                    (map (pexp . (PRef fc []) . fst) bargs_post) ++
                    case mpn of
                         Nothing -> []
                         Just _ -> [pexp (PApp NoFC (PRef NoFC [] eqCon)
                                               [ pimp (sUN "A") Placeholder False
                                               , pimp (sUN "x") Placeholder False
                                               ])])
        logElab 5 ("New RHS " ++ showTmImpls rhs)
        ctxt <- getContext -- New context with block added
        i <- getIState
        ((rhs', defer, is, ctxt', newDecls, highlights, newGName), _) <-
           tclift $ elaborate ctxt (idris_datatypes i) (idris_name i) (sMN 0 "wpatRHS") clhsty initEState
                    (do pbinds i lhs_tm
                        setNextName
                        (ElabResult _ d is ctxt' newDecls highlights newGName) <-
                           erun fc (build i info ERHS opts fname rhs)
                        psolve lhs_tm
                        tt <- get_term
                        return (tt, d, is, ctxt', newDecls, highlights, newGName))
        setContext ctxt'
        processTacticDecls info newDecls
        sendHighlighting highlights
        updateIState $ \i -> i { idris_name = newGName }

        def' <- checkDef fc iderr True defer
        let def'' = map (\(n, (i, top, t, ns)) -> (n, (i, top, t, ns, False, True))) def'
        addDeferred def''
        mapM_ (elabCaseBlock info opts) is
        logElab 5 ("Checked RHS " ++ show rhs')
        (crhs, crhsty) <- recheckC fc id [] rhs'
        return $ (Right (clhs, crhs), lhs)
  where
    getImps (Bind n (Pi _ _ _) t) = pexp Placeholder : getImps t
    getImps _ = []

    mkAuxC pn wname lhs ns ns' (PClauses fc o n cs)
                = do cs' <- mapM (mkAux pn wname lhs ns ns') cs
                     return $ PClauses fc o wname cs'
    mkAuxC pn wname lhs ns ns' d = return $ d

    mkAux pn wname toplhs ns ns' (PClause fc n tm_in (w:ws) rhs wheres)
        = do i <- getIState
             let tm = addImplPat i tm_in
             logElab 2 ("Matching " ++ showTmImpls tm ++ " against " ++
                                      showTmImpls toplhs)
             case matchClause i toplhs tm of
                Left (a,b) -> ifail $ show fc ++ ":with clause does not match top level"
                Right mvars ->
                    do logElab 3 ("Match vars : " ++ show mvars)
                       lhs <- updateLHS n pn wname mvars ns ns' (fullApp tm) w
                       return $ PClause fc wname lhs ws rhs wheres
    mkAux pn wname toplhs ns ns' (PWith fc n tm_in (w:ws) wval pn' withs)
        = do i <- getIState
             let tm = addImplPat i tm_in
             logElab 2 ("Matching " ++ showTmImpls tm ++ " against " ++
                                      showTmImpls toplhs)
             withs' <- mapM (mkAuxC pn wname toplhs ns ns') withs
             case matchClause i toplhs tm of
                Left (a,b) -> trace ("matchClause: " ++ show a ++ " =/= " ++ show b) (ifail $ show fc ++ "with clause does not match top level")
                Right mvars ->
                    do lhs <- updateLHS n pn wname mvars ns ns' (fullApp tm) w
                       return $ PWith fc wname lhs ws wval pn' withs'
    mkAux pn wname toplhs ns ns' c
        = ifail $ show fc ++ ":badly formed with clause"

    addArg (PApp fc f args) w = PApp fc f (args ++ [pexp w])
    addArg (PRef fc hls f) w = PApp fc (PRef fc hls f) [pexp w]

    -- ns, arguments which don't depend on the with argument
    -- ns', arguments which do
    updateLHS n pn wname mvars ns_in ns_in' (PApp fc (PRef fc' hls' n') args) w
        = let ns = map (keepMvar (map fst mvars) fc') ns_in
              ns' = map (keepMvar (map fst mvars) fc') ns_in' in
              return $ substMatches mvars $
                  PApp fc (PRef fc' [] wname)
                      (map pexp ns ++ pexp w : (map pexp ns') ++
                        case pn of
                             Nothing -> []
                             Just pnm -> [pexp (PRef fc [] pnm)])
    updateLHS n pn wname mvars ns_in ns_in' tm w
        = updateLHS n pn wname mvars ns_in ns_in' (PApp fc tm []) w

    -- Only keep a var as a pattern variable in the with block if it's
    -- matched in the top level pattern
    keepMvar mvs fc v | v `elem` mvs = PRef fc [] v
                      | otherwise = Placeholder

    updateWithTerm :: IState -> Maybe Name -> Name -> PTerm -> [Name] -> [Name] -> PTerm -> PTerm
    updateWithTerm ist pn wname toplhs ns_in ns_in' tm 
          = mapPT updateApp tm
       where
         arity (PApp _ _ as) = length as
         arity _ = 0

         lhs_arity = arity toplhs

         updateApp wtm@(PWithApp fcw tm warg) = 
              case matchClause ist toplhs tm of
                Left _ -> PElabError (Msg (show fc ++ ":with application does not match top level"))
                Right mvars -> 
                   let ns = map (keepMvar (map fst mvars) fcw) ns_in
                       ns' = map (keepMvar (map fst mvars) fcw) ns_in' 
                       wty = lookupTyExact wname (tt_ctxt ist)
                       res = substMatches mvars $
                          PApp fcw (PRef fcw [] wname)
                            (map pexp ns ++ pexp warg : (map pexp ns') ++
                                case pn of
                                     Nothing -> []
                                     Just pnm -> [pexp (PRef fc [] pnm)]) in
                          case wty of
                               Nothing -> res -- can't happen!
                               Just ty -> addResolves ty res
         updateApp tm = tm

         addResolves ty (PApp fc f args) = PApp fc f (addResolvesArgs fc ty args)
         addResolves ty tm = tm

         -- if an argument's type is a type class, and is otherwise to
         -- be inferred, then resolve it with instance search
         -- This is something of a hack, because matching on the top level
         -- application won't find this information for us
         addResolvesArgs :: FC -> Term -> [PArg] -> [PArg]
         addResolvesArgs fc (Bind n (Pi _ ty _) sc) (a : args)
             | (P _ cn _, _) <- unApply ty,
               getTm a == Placeholder
                 = case lookupCtxtExact cn (idris_classes ist) of
                        Just _ -> a { getTm = PResolveTC fc } : addResolvesArgs fc sc args
                        Nothing -> a : addResolvesArgs fc sc args
         addResolvesArgs fc (Bind n (Pi _ ty _) sc) (a : args)
                 = a : addResolvesArgs fc sc args
         addResolvesArgs fc _ args = args

    fullApp (PApp _ (PApp fc f args) xs) = fullApp (PApp fc f (args ++ xs))
    fullApp x = x

    split [] rest pre = (reverse pre, rest)
    split deps ((n, ty) : rest) pre
          | n `elem` deps = split (deps \\ [n]) rest ((n, ty) : pre)
          | otherwise = split deps rest ((n, ty) : pre)
    split deps [] pre = (reverse pre, [])

    abstract wn wv wty (n, argty) = (n, substTerm wv (P Bound wn wty) argty)

-- Apply a transformation to all RHSes and nested RHSs
mapRHS :: (PTerm -> PTerm) -> PClause -> PClause
mapRHS f (PClause fc n lhs args rhs ws) 
    = PClause fc n lhs args (f rhs) (map (mapRHSdecl f) ws)
mapRHS f (PWith fc n lhs args warg prf ws)
    = PWith fc n lhs args (f warg) prf (map (mapRHSdecl f) ws)
mapRHS f (PClauseR fc args rhs ws) 
    = PClauseR fc args (f rhs) (map (mapRHSdecl f) ws)
mapRHS f (PWithR fc args warg prf ws)
    = PWithR fc args (f warg) prf (map (mapRHSdecl f) ws)

mapRHSdecl :: (PTerm -> PTerm) -> PDecl -> PDecl
mapRHSdecl f (PClauses fc opt n cs) 
    = PClauses fc opt n (map (mapRHS f) cs)
mapRHSdecl f t = t

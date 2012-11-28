{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards #-}

module Idris.ElabDecls where

import Idris.AbsSyntax
import Idris.DSL
import Idris.Error
import Idris.Delaborate
import Idris.Imports
import Idris.ElabTerm
import Idris.Coverage
import Idris.DataOpts
import Paths_idris

import Core.TT
import Core.Elaborate hiding (Tactic(..))
import Core.Evaluate
import Core.Typecheck
import Core.CaseTree

import Control.Monad
import Control.Monad.State
import Data.List
import Data.Maybe
import Debug.Trace

recheckC fc env t 
    = do -- t' <- applyOpts (forget t) (doesn't work, or speed things up...)
         ctxt <- getContext 
         (tm, ty, cs) <- tclift $ case recheck ctxt env (forget t) t of
                                   Error e -> tfail (At fc e)
                                   OK x -> return x
         addConstraints fc cs
         return (tm, ty)

checkDef fc ns = do ctxt <- getContext
                    mapM (\(n, t) -> do (t', _) <- recheckC fc [] t
                                        return (n, t')) ns

elabType :: ElabInfo -> SyntaxInfo -> String ->
            FC -> FnOpts -> Name -> PTerm -> Idris ()
elabType info syn doc fc opts n ty' = {- let ty' = piBind (params info) ty_in 
                                      n  = liftname info n_in in    -}
      do checkUndefined fc n
         ctxt <- getContext
         i <- get
         logLvl 3 $ show n ++ " pre-type " ++ showImp True ty'
         ty' <- implicit syn n ty'
         let ty = addImpl i ty'
         logLvl 2 $ show n ++ " type " ++ showImp True ty
         ((tyT, defer, is), log) <- tclift $ elaborate ctxt n (Set (UVal 0)) []
                                             (erun fc (build i info False n ty))
         ds <- checkDef fc defer
         addDeferred ds
         mapM_ (elabCaseBlock info) is 
         ctxt <- getContext
         logLvl 5 $ "Rechecking"
         (cty, _)   <- recheckC fc [] tyT
         addStatics n cty ty'
         logLvl 6 $ "Elaborated to " ++ showEnvDbg [] tyT
         logLvl 2 $ "Rechecked to " ++ show cty
         let nty = cty -- normalise ctxt [] cty
         -- if the return type is something coinductive, freeze the definition
         let nty' = normalise ctxt [] nty
         let (t, _) = unApply (getRetTy nty')
         let corec = case t of
                        P _ rcty _ -> case lookupCtxt Nothing rcty (idris_datatypes i) of
                                        [TI _ True] -> True
                                        _ -> False
                        _ -> False
         let opts' = if corec then (Coinductive : opts) else opts
         ds <- checkDef fc [(n, nty)]
         addIBC (IBCDef n)
         addDeferred ds
         setFlags n opts'
         addDocStr n doc
         addIBC (IBCDoc n)
         addIBC (IBCFlags n opts')
         when corec $ do setAccessibility n Frozen
                         addIBC (IBCAccess n Frozen)

elabPostulate :: ElabInfo -> SyntaxInfo -> String ->
                 FC -> FnOpts -> Name -> PTerm -> Idris ()
elabPostulate info syn doc fc opts n ty
    = do elabType info syn doc fc opts n ty
         -- make sure it's collapsible, so it is never needed at run time
         -- start by getting the elaborated type
         ctxt <- getContext
         fty <- case lookupTy Nothing n ctxt of
            [] -> tclift $ tfail $ (At fc (NoTypeDecl n)) -- can't happen!
            [ty] -> return ty
         ist <- get
         let (ap, _) = unApply (getRetTy fty)
         logLvl 5 $ "Checking collapsibility of " ++ show (ap, fty)
         let postOK = case ap of
                            P _ tn _ -> case lookupCtxt Nothing tn
                                                (idris_optimisation ist) of
                                            [oi] -> collapsible oi
                                            _ -> False
                            _ -> False
         when (not postOK)
            $ tclift $ tfail (At fc (NonCollapsiblePostulate n))
         -- remove it from the deferred definitions list
         solveDeferred n

elabData :: ElabInfo -> SyntaxInfo -> String -> FC -> Bool -> PData -> Idris ()
elabData info syn doc fc codata (PLaterdecl n t_in)
    = do iLOG (show (fc, doc))
         checkUndefined fc n
         ctxt <- getContext
         i <- get
         t_in <- implicit syn n t_in
         let t = addImpl i t_in
         ((t', defer, is), log) <- tclift $ elaborate ctxt n (Set (UVal 0)) []
                                            (erun fc (build i info False n t))
         def' <- checkDef fc defer
         addDeferred def'
         mapM_ (elabCaseBlock info) is
         (cty, _)  <- recheckC fc [] t'
         logLvl 2 $ "---> " ++ show cty
         updateContext (addTyDecl n cty) -- temporary, to check cons

elabData info syn doc fc codata (PDatadecl n t_in dcons)
    = do iLOG (show fc)
         undef <- isUndefined fc n
         ctxt <- getContext
         i <- get
         t_in <- implicit syn n t_in
         let t = addImpl i t_in
         ((t', defer, is), log) <- tclift $ elaborate ctxt n (Set (UVal 0)) []
                                            (erun fc (build i info False n t))
         def' <- checkDef fc defer
         addDeferred def'
         mapM_ (elabCaseBlock info) is
         (cty, _)  <- recheckC fc [] t'
         logLvl 2 $ "---> " ++ show cty
         -- temporary, to check cons
         when undef $ updateContext (addTyDecl n cty) 
         cons <- mapM (elabCon info syn n codata) dcons
         ttag <- getName
         i <- get
         put (i { idris_datatypes = addDef n (TI (map fst cons) codata)
                                             (idris_datatypes i) })
         addIBC (IBCDef n)
         addIBC (IBCData n)
         addDocStr n doc
         addIBC (IBCDoc n)
         collapseCons n cons
         updateContext (addDatatype (Data n ttag cty cons))
         mapM_ (checkPositive n) cons

elabRecord :: ElabInfo -> SyntaxInfo -> String -> FC -> Name -> 
              PTerm -> String -> Name -> PTerm -> Idris ()
elabRecord info syn doc fc tyn ty cdoc cn cty
    = do elabData info syn doc fc False (PDatadecl tyn ty [(cdoc, cn, cty, fc)]) 
         cty' <- implicit syn cn cty
         i <- get
         cty <- case lookupTy Nothing cn (tt_ctxt i) of
                    [t] -> return (delab i t)
                    _ -> fail "Something went inexplicably wrong"
         cimp <- case lookupCtxt Nothing cn (idris_implicits i) of
                    [imps] -> return imps
         let ptys = getProjs [] (renameBs cimp cty)
         let ptys_u = getProjs [] cty
         let recty = getRecTy cty
         logLvl 6 $ show (recty, ptys)
         let substs = map (\ (n, _) -> (n, PApp fc (PRef fc n)
                                                [pexp (PRef fc rec)])) ptys
         proj_decls <- mapM (mkProj recty substs cimp) (zip ptys [0..])
         let nonImp = mapMaybe isNonImp (zip cimp ptys_u)
         let implBinds = getImplB id cty'
         update_decls <- mapM (mkUpdate recty implBinds (length nonImp)) (zip nonImp [0..])
         mapM_ (elabDecl EAll info) (concat proj_decls)
         mapM_ (tryElabDecl info) (update_decls)
  where
--     syn = syn_in { syn_namespace = show (nsroot tyn) : syn_namespace syn_in }

    isNonImp (PExp _ _ _ _, a) = Just a
    isNonImp _ = Nothing

    tryElabDecl info (fn, ty, val)
        = do i <- get
             idrisCatch (do elabDecl' EAll info ty
                            elabDecl' EAll info val)
                        (\v -> do iputStrLn $ show fc ++ 
                                      ":Warning - can't generate setter for " ++ 
                                      show fn ++ " (" ++ show ty ++ ")"
                                  put i)

    getImplB k (PPi (Imp l s _) n Placeholder sc)
        = getImplB k sc
    getImplB k (PPi (Imp l s d) n ty sc)
        = getImplB (\x -> k (PPi (Imp l s d) n ty x)) sc
    getImplB k (PPi _ n ty sc)
        = getImplB k sc
    getImplB k _ = k

    renameBs (PImp _ _ _ _ _ : ps) (PPi p n ty s)
        = PPi p (mkImp n) ty (renameBs ps (substMatch n (PRef fc (mkImp n)) s))
    renameBs (_:ps) (PPi p n ty s) = PPi p n ty (renameBs ps s)
    renameBs _ t = t

    getProjs acc (PPi _ n ty s) = getProjs ((n, ty) : acc) s
    getProjs acc r = reverse acc

    getRecTy (PPi _ n ty s) = getRecTy s
    getRecTy t = t

    rec = MN 0 "rec"

    mkp (UN n) = MN 0 ("p_" ++ n)
    mkp (MN i n) = MN i ("p_" ++ n)
    mkp (NS n s) = NS (mkp n) s

    mkImp (UN n) = UN ("implicit_" ++ n)
    mkImp (MN i n) = MN i ("implicit_" ++ n)
    mkImp (NS n s) = NS (mkImp n) s

    mkSet (UN n) = UN ("set_" ++ n)
    mkSet (MN i n) = MN i ("set_" ++ n)
    mkSet (NS n s) = NS (mkSet n) s

    mkProj recty substs cimp ((pn_in, pty), pos)
        = do let pn = expandNS syn pn_in
             let pfnTy = PTy "" defaultSyntax fc [] pn
                            (PPi expl rec recty
                               (substMatches substs pty))
             let pls = repeat Placeholder
             let before = pos
             let after = length substs - (pos + 1)
             let args = take before pls ++ PRef fc (mkp pn) : take after pls
             let iargs = map implicitise (zip cimp args)
             let lhs = PApp fc (PRef fc pn)
                        [pexp (PApp fc (PRef fc cn) iargs)]
             let rhs = PRef fc (mkp pn)
             let pclause = PClause fc pn lhs [] rhs [] 
             return [pfnTy, PClauses fc [] pn [pclause]]
          
    implicitise (pa, t) = pa { getTm = t }

    mkUpdate recty k num ((pn, pty), pos)
       = do let setname = expandNS syn $ mkSet pn
            let valname = MN 0 "updateval"
            let pt = k (PPi expl pn pty
                           (PPi expl rec recty recty))
            let pfnTy = PTy "" defaultSyntax fc [] setname pt
            let pls = map (\x -> PRef fc (MN x "field")) [0..num-1]
            let lhsArgs = pls
            let rhsArgs = take pos pls ++ (PRef fc valname) :
                               drop (pos + 1) pls
            let before = pos
            let pclause = PClause fc setname (PApp fc (PRef fc setname)
                                              [pexp (PRef fc valname),
                                               pexp (PApp fc (PRef fc cn)
                                                        (map pexp lhsArgs))])
                                             []
                                             (PApp fc (PRef fc cn)
                                                      (map pexp rhsArgs)) []
            return (pn, pfnTy, PClauses fc [] setname [pclause])

elabCon :: ElabInfo -> SyntaxInfo -> Name -> Bool -> 
           (String, Name, PTerm, FC) -> Idris (Name, Type)
elabCon info syn tn codata (doc, n, t_in, fc)
    = do checkUndefined fc n
         ctxt <- getContext
         i <- get
         t_in <- implicit syn n (if codata then mkLazy t_in else t_in)
         let t = addImpl i t_in
         logLvl 2 $ show fc ++ ":Constructor " ++ show n ++ " : " ++ showImp True t
         ((t', defer, is), log) <- tclift $ elaborate ctxt n (Set (UVal 0)) []
                                            (erun fc (build i info False n t))
         logLvl 2 $ "Rechecking " ++ show t'
         def' <- checkDef fc defer
         addDeferred def'
         mapM_ (elabCaseBlock info) is
         ctxt <- getContext
         (cty, _)  <- recheckC fc [] t'
         let cty' = normaliseC ctxt [] cty
         tyIs cty'
         logLvl 2 $ "---> " ++ show n ++ " : " ++ show cty'
         addIBC (IBCDef n)
         addDocStr n doc
         addIBC (IBCDoc n)
         forceArgs n cty'
         return (n, cty')
  where
    tyIs (Bind n b sc) = tyIs sc
    tyIs t | (P _ n' _, _) <- unApply t 
        = if n' /= tn then tclift $ tfail (At fc (Msg (show n' ++ " is not " ++ show tn))) 
             else return ()
    tyIs t = tclift $ tfail (At fc (Msg (show t ++ " is not " ++ show tn)))

    mkLazy (PPi pl n ty sc) = PPi (pl { plazy = True }) n ty (mkLazy sc)
    mkLazy t = t

elabClauses :: ElabInfo -> FC -> FnOpts -> Name -> [PClause] -> Idris ()
elabClauses info fc opts n_in cs = let n = liftname info n_in in  
      do ctxt <- getContext
         -- Check n actually exists
         let tys = lookupTy Nothing n ctxt
         unless (length tys > 1) $ do
           fty <- case tys of
              [] -> -- TODO: turn into a CAF if there's no arguments
                    -- question: CAFs in where blocks?
                    tclift $ tfail $ At fc (NoTypeDecl n)
              [ty] -> return ty
           pats_in <- mapM (elabClause info (TCGen `elem` opts)) 
                           (zip [0..] cs)
           -- if the return type of 'ty' is collapsible, the optimised version should
           -- just do nothing
           ist <- get
           let (ap, _) = unApply (getRetTy fty)
           logLvl 5 $ "Checking collapsibility of " ++ show (ap, fty)
           -- FIXME: Really ought to only do this for total functions!
           let doNothing = case ap of
                              P _ tn _ -> case lookupCtxt Nothing tn
                                                  (idris_optimisation ist) of
                                              [oi] -> collapsible oi
                                              _ -> False
                              _ -> False
           solveDeferred n
           ist <- get
           when doNothing $ 
              case lookupCtxt Nothing n (idris_optimisation ist) of
                 [oi] -> do let opts = addDef n (oi { collapsible = True }) 
                                           (idris_optimisation ist)
                            put (ist { idris_optimisation = opts })
                 _ -> do let opts = addDef n (Optimise True [] [])
                                           (idris_optimisation ist)
                         put (ist { idris_optimisation = opts })
                         addIBC (IBCOpt n)
           ist <- get
           let pats = pats_in
  --          logLvl 3 (showSep "\n" (map (\ (l,r) -> 
  --                                         show l ++ " = " ++ 
  --                                         show r) pats))
           let tcase = opt_typecase (idris_options ist)
           let pdef = map debind $ map (simpl False (tt_ctxt ist)) pats
           
           numArgs <- tclift $ sameLength pdef

           optpats <- if doNothing 
                         then return $ [Right (mkApp (P Bound n Erased)
                                                    (take numArgs (repeat Erased)), Erased)]
                         else stripCollapsed pats

           logLvl 5 $ "Patterns:\n" ++ show pats

           let optpdef = map debind $ map (simpl True (tt_ctxt ist)) optpats
           tree@(CaseDef scargs sc _) <- tclift $ 
                   simpleCase tcase False CompileTime fc pdef
           cov <- coverage
           pmissing <-
                   if cov  
                      then do missing <- genClauses fc n (map getLHS pdef) cs
                              -- missing <- genMissing n scargs sc  
                              missing' <- filterM (checkPossible info fc True n) missing
                              logLvl 2 $ "Must be unreachable:\n" ++ 
                                          showSep "\n" (map (showImp True) missing') ++
                                         "\nAgainst: " ++
                                          showSep "\n" (map (\t -> showImp True (delab ist t)) (map getLHS pdef))
                              return missing'
                      else return []
           let pcover = null pmissing
           pdef' <- applyOpts optpdef 
           logLvl 5 $ "Optimised patterns:\n" ++ show pdef'
           ist <- get
  --          let wf = wellFounded ist n sc
           let tot = if pcover || AssertTotal `elem` opts
                      then Unchecked -- finish checking later
                      else Partial NotCovering -- already know it's not total
  --          case lookupCtxt (namespace info) n (idris_flags ist) of 
  --             [fs] -> if TotalFn `elem` fs 
  --                       then case tot of
  --                               Total _ -> return ()
  --                               t -> tclift $ tfail (At fc (Msg (show n ++ " is " ++ show t)))
  --                       else return ()
  --             _ -> return ()
           case tree of
               CaseDef _ _ [] -> return ()
               CaseDef _ _ xs -> mapM_ (\x ->
                   iputStrLn $ show fc ++
                                ":warning - Unreachable case: " ++ 
                                   show (delab ist x)) xs
           let knowncovering = pcover && cov

           tree' <- tclift $ simpleCase tcase knowncovering RunTime fc pdef'
           logLvl 3 (show tree)
           logLvl 3 $ "Optimised: " ++ show tree'
           ctxt <- getContext
           ist <- get
           put (ist { idris_patdefs = addDef n pdef' (idris_patdefs ist) })
           case lookupTy (namespace info) n ctxt of
               [ty] -> do updateContext (addCasedef n (inlinable opts)
                                                       tcase knowncovering pats
                                                       pdef pdef' ty)
                          addIBC (IBCDef n)
                          setTotality n tot
                          totcheck (fc, n)
                          when (tot /= Unchecked) $ addIBC (IBCTotal n tot)
                          i <- get
                          case lookupDef Nothing n (tt_ctxt i) of
                              (CaseOp _ _ _ _ _ scargs sc scargs' sc' : _) ->
                                  do let calls = findCalls sc' scargs'
                                     let used = findUsedArgs sc' scargs'
                                     -- let scg = buildSCG i sc scargs
                                     -- add SCG later, when checking totality
                                     let cg = CGInfo scargs' calls [] used []
                                     logLvl 2 $ "Called names: " ++ show cg
                                     addToCG n cg
                                     addToCalledG n (nub (map fst calls)) -- plus names in type!
                                     addIBC (IBCCG n)
                              _ -> return ()
  --                         addIBC (IBCTotal n tot)
               [] -> return ()
           return ()
  where
    debind (Right (x, y)) = let (vs, x') = depat [] x 
                                (_, y') = depat [] y in
                                (vs, x', y')
    debind (Left x)       = let (vs, x') = depat [] x in
                                (vs, x', Impossible)

    depat acc (Bind n (PVar t) sc) = depat (n : acc) (instantiate (P Bound n t) sc)
    depat acc x = (acc, x)
    
    getLHS (_, l, _) = l

    simpl rt ctxt (Right (x, y)) = Right (normalise ctxt [] x,
                                          simplify ctxt rt [] y)
    simpl rt ctxt t = t

    sameLength ((_, x, _) : xs) 
        = do l <- sameLength xs
             let (f, as) = unApply x
             if (null xs || l == length as) then return (length as)
                else tfail (At fc (Msg "Clauses have differing numbers of arguments "))
    sameLength [] = return 0

elabVal :: ElabInfo -> Bool -> PTerm -> Idris (Term, Type)
elabVal info aspat tm_in
   = do ctxt <- getContext
        i <- get
        let tm = addImpl i tm_in
        logLvl 10 (showImp True tm)
        -- try:
        --    * ordinary elaboration
        --    * elaboration as a Set
        --    * elaboration as a function a -> b
        
        ((tm', defer, is), _) <- 
            tctry (elaborate ctxt (MN 0 "val") (Set (UVal 0)) []                         
                       (build i info aspat (MN 0 "val") tm))
                  (elaborate ctxt (MN 0 "val") infP []
                        (build i info aspat (MN 0 "val") (infTerm tm)))
        logLvl 3 ("Value: " ++ show tm')
        let vtm = getInferTerm tm'
        logLvl 2 (show vtm)
        recheckC (FC "(input)" 0) [] vtm

-- checks if the clause is a possible left hand side. Returns the term if
-- possible, otherwise Nothing.

checkPossible :: ElabInfo -> FC -> Bool -> Name -> PTerm -> Idris Bool
checkPossible info fc tcgen fname lhs_in
   = do ctxt <- getContext
        i <- get
        let lhs = addImpl i lhs_in
        -- if the LHS type checks, it is possible
        case elaborate ctxt (MN 0 "patLHS") infP []
                            (erun fc (buildTC i info True tcgen fname (infTerm lhs))) of
            OK ((lhs', _, _), _) ->
               do let lhs_tm = orderPats (getInferTerm lhs')
                  case recheck ctxt [] (forget lhs_tm) lhs_tm of
                       OK _ -> return True
                       _ -> return False
--                   b <- inferredDiff fc (delab' i lhs_tm True) lhs
--                   return (not b) -- then return (Just lhs_tm) else return Nothing
--                   trace (show (delab' i lhs_tm True) ++ "\n" ++ show lhs) $ return (not b)
            Error _ -> return False

elabClause :: ElabInfo -> Bool -> (Int, PClause) -> 
              Idris (Either Term (Term, Term))
elabClause info tcgen (_, PClause fc fname lhs_in [] PImpossible [])
   = do b <- checkPossible info fc tcgen fname lhs_in
        case b of
            True -> fail $ show fc ++ ":" ++ show lhs_in ++ " is a possible case"
            False -> do ptm <- mkPatTm lhs_in
                        return (Left ptm)
elabClause info tcgen (cnum, PClause fc fname lhs_in withs rhs_in whereblock) 
   = do ctxt <- getContext
        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        i <- get
        let lhs = addImplPat i lhs_in
        logLvl 5 ("LHS: " ++ show fc ++ " " ++ showImp True lhs)
        ((lhs', dlhs, []), _) <- 
            tclift $ elaborate ctxt (MN 0 "patLHS") infP []
                     (erun fc (buildTC i info True tcgen fname (infTerm lhs)))
        let lhs_tm = orderPats (getInferTerm lhs')
        let lhs_ty = getInferType lhs'
        logLvl 3 ("Elaborated: " ++ show lhs_tm)
        (clhs, clhsty) <- recheckC fc [] lhs_tm
        logLvl 5 ("Checked " ++ show clhs)
        -- Elaborate where block
        ist <- getIState
        windex <- getName
        let winfo = pinfo (pvars ist lhs_tm) whereblock windex
        let decls = nub (concatMap declared whereblock)
        let defs = nub (decls ++ concatMap defined whereblock)
        let newargs = pvars ist lhs_tm
        let wb = map (expandParamsD False ist decorate newargs defs) whereblock
        
        -- Split the where block into declarations with a type, and those
        -- without
        -- Elaborate those with a type *before* RHS, those without *after*
        let (wbefore, wafter) = sepBlocks wb

        logLvl 5 $ "Where block:\n " ++ show wbefore ++ "\n" ++ show wafter
        mapM_ (elabDecl' EAll info) wbefore
        -- Now build the RHS, using the type of the LHS as the goal.
        i <- get -- new implicits from where block
        logLvl 5 (showImp True (expandParams decorate newargs defs (defs \\ decls) rhs_in))
        let rhs = addImplBoundInf i (map fst newargs) (defs \\ decls)
                                 (expandParams decorate newargs defs (defs \\ decls) rhs_in)
        logLvl 2 $ "RHS: " ++ showImp True rhs
        ctxt <- getContext -- new context with where block added
        logLvl 5 "STARTING CHECK"
        ((rhs', defer, is), _) <- 
           tclift $ elaborate ctxt (MN 0 "patRHS") clhsty []
                    (do pbinds lhs_tm
                        (_, _, is) <- erun fc (build i info False fname rhs)
                        erun fc $ psolve lhs_tm
                        tt <- get_term
                        let (tm, ds) = runState (collectDeferred tt) []
                        return (tm, ds, is))
        logLvl 5 "DONE CHECK"
        logLvl 2 $ "---> " ++ show rhs'
        when (not (null defer)) $ iLOG $ "DEFERRED " ++ show defer
        def' <- checkDef fc defer
        addDeferred def'

        -- Now the remaining deferred (i.e. no type declarations) clauses
        -- from the where block

        mapM_ (elabDecl' EAll info) wafter
        mapM_ (elabCaseBlock info) is

        ctxt <- getContext
        logLvl 5 $ "Rechecking"
        (crhs, crhsty) <- recheckC fc [] rhs'
        logLvl 6 $ " ==> " ++ show crhsty ++ "   against   " ++ show clhsty
        case  converts ctxt [] clhsty crhsty of
            OK _ -> return ()
            Error _ -> ierror (At fc (CantUnify False clhsty crhsty (Msg "") [] 0))
        i <- get
        checkInferred fc (delab' i crhs True) rhs
        return $ Right (clhs, crhs)
  where
    decorate (NS x ns) = NS (UN ('#':show x)) (ns ++ [show cnum, show fname])
    decorate x = NS (UN ('#':show x)) [show cnum, show fname]

    sepBlocks bs = sepBlocks' [] bs where
      sepBlocks' ns (d@(PTy _ _ _ _ n t) : bs)
            = let (bf, af) = sepBlocks' (n : ns) bs in
                  (d : bf, af)
      sepBlocks' ns (d@(PClauses _ _ n _) : bs) 
         | not (n `elem` ns) = let (bf, af) = sepBlocks' ns bs in
                                   (bf, d : af)
      sepBlocks' ns (b : bs) = let (bf, af) = sepBlocks' ns bs in
                                   (b : bf, af)
      sepBlocks' ns [] = ([], [])

    pinfo ns ps i 
          = let ds = concatMap declared ps
                newps = params info ++ ns
                dsParams = map (\n -> (n, map fst newps)) ds
                newb = addAlist dsParams (inblock info) 
                l = liftname info in
                info { params = newps,
                       inblock = newb,
                       liftname = id -- (\n -> case lookupCtxt n newb of
                                     --      Nothing -> n
                                     --      _ -> MN i (show n)) . l
                    }

elabClause info tcgen (_, PWith fc fname lhs_in withs wval_in withblock) 
   = do ctxt <- getContext
        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        i <- get
        let lhs = addImpl i lhs_in
        logLvl 5 ("LHS: " ++ showImp True lhs)
        ((lhs', dlhs, []), _) <- 
            tclift $ elaborate ctxt (MN 0 "patLHS") infP []
              (erun fc (buildTC i info True tcgen fname (infTerm lhs))) 
        let lhs_tm = orderPats (getInferTerm lhs')
        let lhs_ty = getInferType lhs'
        let ret_ty = getRetTy lhs_ty
        logLvl 3 (show lhs_tm)
        (clhs, clhsty) <- recheckC fc [] lhs_tm
        logLvl 5 ("Checked " ++ show clhs)
        let bargs = getPBtys lhs_tm
        let wval = addImplBound i (map fst bargs) wval_in
        logLvl 5 ("Checking " ++ showImp True wval)
        -- Elaborate wval in this context
        ((wval', defer, is), _) <- 
            tclift $ elaborate ctxt (MN 0 "withRHS") 
                        (bindTyArgs PVTy bargs infP) []
                        (do pbinds lhs_tm
                            -- TODO: may want where here - see winfo abpve
                            (_', d, is) <- erun fc (build i info False fname (infTerm wval))
                            erun fc $ psolve lhs_tm
                            tt <- get_term
                            return (tt, d, is))
        def' <- checkDef fc defer
        addDeferred def'
        mapM_ (elabCaseBlock info) is
        (cwval, cwvalty) <- recheckC fc [] (getInferTerm wval')
        logLvl 3 ("With type " ++ show cwvalty ++ "\nRet type " ++ show ret_ty)
        windex <- getName
        -- build a type declaration for the new function:
        -- (ps : Xs) -> (withval : cwvalty) -> ret_ty 
        let wtype = bindTyArgs Pi (bargs ++ [(MN 0 "warg", getRetTy cwvalty)]) ret_ty
        logLvl 3 ("New function type " ++ show wtype)
        let wname = MN windex (show fname)
        let imps = getImps wtype -- add to implicits context
        put (i { idris_implicits = addDef wname imps (idris_implicits i) })
        addIBC (IBCDef wname)
        def' <- checkDef fc [(wname, wtype)]
        addDeferred def'

        -- in the subdecls, lhs becomes:
        --         fname  pats | wpat [rest]
        --    ==>  fname' ps   wpat [rest], match pats against toplevel for ps
        wb <- mapM (mkAuxC wname lhs (map fst bargs)) withblock
        logLvl 5 ("with block " ++ show wb)
        mapM_ (elabDecl EAll info) wb

        -- rhs becomes: fname' ps wval
        let rhs = PApp fc (PRef fc wname) (map (pexp . (PRef fc) . fst) bargs ++ 
                                                [pexp wval])
        logLvl 3 ("New RHS " ++ show rhs)
        ctxt <- getContext -- New context with block added
        i <- get
        ((rhs', defer, is), _) <-
           tclift $ elaborate ctxt (MN 0 "wpatRHS") clhsty []
                    (do pbinds lhs_tm
                        (_, d, is) <- erun fc (build i info False fname rhs)
                        psolve lhs_tm
                        tt <- get_term
                        return (tt, d, is))
        def' <- checkDef fc defer
        addDeferred def'
        mapM_ (elabCaseBlock info) is
        (crhs, crhsty) <- recheckC fc [] rhs'
        return $ Right (clhs, crhs)
  where
    getImps (Bind n (Pi _) t) = pexp Placeholder : getImps t
    getImps _ = []

    mkAuxC wname lhs ns (PClauses fc o n cs)
        | True  = do cs' <- mapM (mkAux wname lhs ns) cs
                     return $ PClauses fc o wname cs'
        | otherwise = fail $ show fc ++ "with clause uses wrong function name " ++ show n
    mkAuxC wname lhs ns d = return $ d

    mkAux wname toplhs ns (PClause fc n tm_in (w:ws) rhs wheres)
        = do i <- get
             let tm = addImpl i tm_in
             logLvl 2 ("Matching " ++ showImp True tm ++ " against " ++ 
                                      showImp True toplhs)
             case matchClause i toplhs tm of
                Left _ -> fail $ show fc ++ "with clause does not match top level"
                Right mvars -> do logLvl 3 ("Match vars : " ++ show mvars)
                                  lhs <- updateLHS n wname mvars ns (fullApp tm) w
                                  return $ PClause fc wname lhs ws rhs wheres
    mkAux wname toplhs ns (PWith fc n tm_in (w:ws) wval withs)
        = do i <- get
             let tm = addImpl i tm_in
             logLvl 2 ("Matching " ++ showImp True tm ++ " against " ++ 
                                      showImp True toplhs)
             withs' <- mapM (mkAuxC wname toplhs ns) withs
             case matchClause i toplhs tm of
                Left _ -> fail $ show fc ++ "with clause does not match top level"
                Right mvars -> do lhs <- updateLHS n wname mvars ns (fullApp tm) w
                                  return $ PWith fc wname lhs ws wval withs'
    mkAux wname toplhs ns c
        = fail $ show fc ++ "badly formed with clause"

    updateLHS n wname mvars ns (PApp fc (PRef fc' n') args) w
        = let ns' = map (keepMvar (map fst mvars) fc') ns in
              return $ substMatches mvars $ 
                  PApp fc (PRef fc' wname) 
                      (map pexp ns' ++ [pexp w])
    updateLHS n wname mvars ns tm w = fail $ "Not implemented match " ++ show tm 

    keepMvar mvs fc v | v `elem` mvs = PRef fc v
                      | otherwise = Placeholder

    fullApp (PApp _ (PApp fc f args) xs) = fullApp (PApp fc f (args ++ xs))
    fullApp x = x

data MArgTy = IA | EA | CA deriving Show

elabClass :: ElabInfo -> SyntaxInfo -> String ->
             FC -> [PTerm] -> 
             Name -> [(Name, PTerm)] -> [PDecl] -> Idris ()
elabClass info syn doc fc constraints tn ps ds 
    = do let cn = UN ("instance" ++ show tn) -- MN 0 ("instance" ++ show tn)
         let tty = pibind ps PSet
         let constraint = PApp fc (PRef fc tn)
                                  (map (pexp . PRef fc) (map fst ps))
         -- build data declaration
         let mdecls = filter tydecl ds -- method declarations
         let mnames = map getMName mdecls
         logLvl 2 $ "Building methods " ++ show mnames
         ims <- mapM (tdecl mnames) mdecls
         defs <- mapM (defdecl (map (\ (x,y,z) -> z) ims) constraint) 
                      (filter clause ds)
         let (methods, imethods) 
              = unzip (map (\ ( x,y,z) -> (x, y)) ims)
         -- build instance constructor type
         -- decorate names of functions to ensure they can't be referred
         -- to elsewhere in the class declaration
         let cty = impbind ps $ conbind constraints 
                      $ pibind (map (\ (n, ty) -> (mdec n, ty)) methods) 
                               constraint
         let cons = [("", cn, cty, fc)]
         let ddecl = PDatadecl tn tty cons
         logLvl 5 $ "Class data " ++ showDImp True ddecl
         elabData info (syn { no_imp = no_imp syn ++ mnames }) doc fc False ddecl
         -- for each constraint, build a top level function to chase it
         logLvl 5 $ "Building functions"
         let usyn = syn { using = ps ++ using syn }
         fns <- mapM (cfun cn constraint usyn (map fst imethods)) constraints
         mapM_ (elabDecl EAll info) (concat fns)
         -- for each method, build a top level function
         fns <- mapM (tfun cn constraint usyn (map fst imethods)) imethods
         mapM_ (elabDecl EAll info) (concat fns)
         -- add the default definitions
         mapM_ (elabDecl EAll info) (concat (map (snd.snd) defs))
         i <- get
         let defaults = map (\ (x, (y, z)) -> (x,y)) defs
         addClass tn (CI cn (map nodoc imethods) defaults (map fst ps) []) 
         addIBC (IBCClass tn)
  where
    nodoc (n, (_, o, t)) = (n, (o, t))
    pibind [] x = x
    pibind ((n, ty): ns) x = PPi expl n ty (pibind ns x) 

    mdec (UN n) = (UN ('!':n))
    mdec (NS x n) = NS (mdec x) n
    mdec x = x

    impbind [] x = x
    impbind ((n, ty): ns) x = PPi impl n ty (impbind ns x) 
    conbind (ty : ns) x = PPi constraint (MN 0 "c") ty (conbind ns x)
    conbind [] x = x

    getMName (PTy _ _ _ _ n _) = nsroot n
    tdecl allmeths (PTy doc syn _ o n t) 
           = do t' <- implicit' syn allmeths n t
                logLvl 5 $ "Method " ++ show n ++ " : " ++ showImp True t'
                return ( (n, (toExp (map fst ps) Exp t')),
                         (n, (doc, o, (toExp (map fst ps) Imp t'))),
                         (n, (syn, o, t) ) )
    tdecl _ _ = fail "Not allowed in a class declaration"

    -- Create default definitions 
    defdecl mtys c d@(PClauses fc opts n cs) =
        case lookup n mtys of
            Just (syn, o, ty) -> do let ty' = insertConstraint c ty
                                    let ds = map (decorateid defaultdec)
                                                 [PTy "" syn fc [] n ty', 
                                                  PClauses fc (TCGen:o ++ opts) n cs]
                                    iLOG (show ds)
                                    return (n, ((defaultdec n, ds!!1), ds))
            _ -> fail $ show n ++ " is not a method"
    defdecl _ _ _ = fail "Can't happen (defdecl)"

    defaultdec (UN n) = UN ("default#" ++ n)
    defaultdec (NS n ns) = NS (defaultdec n) ns

    tydecl (PTy _ _ _ _ _ _) = True
    tydecl _ = False
    clause (PClauses _ _ _ _) = True
    clause _ = False

    cfun cn c syn all con
        = do let cfn = UN ('@':'@':show cn ++ "#" ++ show con)
             let mnames = take (length all) $ map (\x -> MN x "meth") [0..]
             let capp = PApp fc (PRef fc cn) (map (pexp . PRef fc) mnames)
             let lhs = PApp fc (PRef fc cfn) [pconst capp]
             let rhs = PResolveTC (FC "HACK" 0)
             let ty = PPi constraint (MN 0 "pc") c con
             iLOG (showImp True ty)
             iLOG (showImp True lhs ++ " = " ++ showImp True rhs)
             i <- get
             let conn = case con of
                            PRef _ n -> n
                            PApp _ (PRef _ n) _ -> n
             let conn' = case lookupCtxtName Nothing conn (idris_classes i) of
                                [(n, _)] -> n
                                _ -> conn
             addInstance False conn' cfn
             addIBC (IBCInstance False conn' cfn)
--              iputStrLn ("Added " ++ show (conn, cfn, ty))
             return [PTy "" syn fc [] cfn ty,
                     PClauses fc [Inlinable,TCGen] cfn [PClause fc cfn lhs [] rhs []]]

    tfun cn c syn all (m, (doc, o, ty)) 
        = do let ty' = insertConstraint c ty
             let mnames = take (length all) $ map (\x -> MN x "meth") [0..]
             let capp = PApp fc (PRef fc cn) (map (pexp . PRef fc) mnames)
             let margs = getMArgs ty
             let anames = map (\x -> MN x "arg") [0..]
             let lhs = PApp fc (PRef fc m) (pconst capp : lhsArgs margs anames)
             let rhs = PApp fc (getMeth mnames all m) (rhsArgs margs anames)
             iLOG (showImp True ty)
             iLOG (show (m, ty', capp, margs))
             iLOG (showImp True lhs ++ " = " ++ showImp True rhs)
             return [PTy doc syn fc o m ty',
                     PClauses fc [Inlinable,TCGen] m [PClause fc m lhs [] rhs []]]

    getMArgs (PPi (Imp _ _ _) n ty sc) = IA : getMArgs sc
    getMArgs (PPi (Exp _ _ _) n ty sc) = EA  : getMArgs sc
    getMArgs (PPi (Constraint _ _ _) n ty sc) = CA : getMArgs sc
    getMArgs _ = []

    getMeth (m:ms) (a:as) x | x == a = PRef fc m
                            | otherwise = getMeth ms as x

    lhsArgs (EA : xs) (n : ns) = pexp (PRef fc n) : lhsArgs xs ns 
    lhsArgs (IA : xs) ns = lhsArgs xs ns 
    lhsArgs (CA : xs) ns = lhsArgs xs ns
    lhsArgs [] _ = []

    rhsArgs (EA : xs) (n : ns) = pexp (PRef fc n) : rhsArgs xs ns 
    rhsArgs (IA : xs) ns = pexp Placeholder : rhsArgs xs ns 
    rhsArgs (CA : xs) ns = pconst (PResolveTC fc) : rhsArgs xs ns
    rhsArgs [] _ = []

    insertConstraint c (PPi p@(Imp _ _ _) n ty sc)
                          = PPi p n ty (insertConstraint c sc)
    insertConstraint c sc = PPi constraint (MN 0 "c") c sc

    -- make arguments explicit and don't bind class parameters
    toExp ns e (PPi (Imp l s _) n ty sc)
        | n `elem` ns = toExp ns e sc
        | otherwise = PPi (e l s "") n ty (toExp ns e sc)
    toExp ns e (PPi p n ty sc) = PPi p n ty (toExp ns e sc)
    toExp ns e sc = sc

elabInstance :: ElabInfo -> SyntaxInfo -> 
                FC -> [PTerm] -> -- constraints
                Name -> -- the class 
                [PTerm] -> -- class parameters (i.e. instance) 
                PTerm -> -- full instance type
                Maybe Name -> -- explicit name
                [PDecl] -> Idris ()
elabInstance info syn fc cs n ps t expn ds
    = do i <- get 
         (n, ci) <- case lookupCtxtName (namespace info) n (idris_classes i) of
                       [c] -> return c
                       _ -> fail $ show fc ++ ":" ++ show n ++ " is not a type class"
         let iname = case expn of
                         Nothing -> UN ('@':show n ++ "$" ++ show ps)
                         Just nm -> nm
         -- if the instance type matches any of the instances we have already,
         -- and it's not a named instance, then it's overlapping, so report an error
         case expn of
            Nothing -> do mapM_ (checkNotOverlapping i t) (class_instances ci) 
                          addInstance intInst n iname
            Just _ -> addInstance intInst n iname 
         elabType info syn "" fc [] iname t
         let ips = zip (class_params ci) ps
         let ns = case n of
                    NS n ns' -> ns'
                    _ -> []
         -- get the implicit parameters that need passing through to the 
         -- where block
         wparams <- mapM (\p -> case p of
                                  PApp _ _ args -> getWParams args
                                  _ -> return []) ps
         let pnames = map pname (concat (nub wparams))
         let mtys = map (\ (n, (op, t)) -> 
                             let t' = substMatchesShadow ips pnames t in
                                 (decorate ns iname n, 
                                     op, coninsert cs t', t'))
                        (class_methods ci)
         logLvl 3 (show (mtys, ips))
         let ds' = insertDefaults i iname (class_defaults ci) ns ds
         iLOG ("Defaults inserted: " ++ show ds' ++ "\n" ++ show ci)
         mapM_ (warnMissing ds' ns iname) (map fst (class_methods ci))
         mapM_ (checkInClass (map fst (class_methods ci))) (concatMap defined ds')
         let wbTys = map mkTyDecl mtys
         let wbVals = map (decorateid (decorate ns iname)) ds'
         let wb = wbTys ++ wbVals
         logLvl 3 $ "Method types " ++ showSep "\n" (map (showDeclImp True . mkTyDecl) mtys)
         logLvl 3 $ "Instance is " ++ show ps ++ " implicits " ++ 
                                      show (concat (nub wparams))
         let lhs = case concat (nub wparams) of
                        [] -> PRef fc iname
                        as -> PApp fc (PRef fc iname) as
         let rhs = PApp fc (PRef fc (instanceName ci))
                           (map (pexp . mkMethApp) mtys)
         let idecls = [PClauses fc [Inlinable, TCGen] iname 
                                 [PClause fc iname lhs [] rhs wb]]
         iLOG (show idecls)
         mapM (elabDecl EAll info) idecls
         addIBC (IBCInstance intInst n iname)
  where
    intInst = case ps of
                [PConstant IType] -> True
                _ -> False

    checkNotOverlapping i t n
     | take 2 (show n) == "@@" = return ()
     | otherwise
        = case lookupTy Nothing n (tt_ctxt i) of
            [t'] -> let tret = getRetType t
                        tret' = getRetType (delab i t') in
                        case matchClause i tret' tret of
                            Right _ -> overlapping tret tret'
                            Left _ -> case matchClause i tret tret' of
                                Right _ -> overlapping tret tret'
                                Left _ -> return ()
            _ -> return ()
    overlapping t t' = tclift $ tfail (At fc (Msg $ 
                            "Overlapping instance: " ++ show t' ++ " already defined"))
    getRetType (PPi _ _ _ sc) = getRetType sc
    getRetType t = t

    mkMethApp (n, _, _, ty) 
          = lamBind 0 ty (papp fc (PRef fc n) (methArgs 0 ty))
    lamBind i (PPi (Constraint _ _ _) _ _ sc) sc' 
          = PLam (MN i "meth") Placeholder (lamBind (i+1) sc sc')
    lamBind i (PPi _ n ty sc) sc' 
          = PLam (MN i "meth") Placeholder (lamBind (i+1) sc sc')
    lamBind i _ sc = sc
    methArgs i (PPi (Imp _ _ _) n ty sc) 
        = PImp 0 False n (PRef fc (MN i "meth")) "" : methArgs (i+1) sc
    methArgs i (PPi (Exp _ _ _) n ty sc) 
        = PExp 0 False (PRef fc (MN i "meth")) "" : methArgs (i+1) sc
    methArgs i (PPi (Constraint _ _ _) n ty sc) 
        = PConstraint 0 False (PResolveTC fc) "" : methArgs (i+1) sc
    methArgs i _ = []

    papp fc f [] = f
    papp fc f as = PApp fc f as

    getWParams [] = return []
    getWParams (p : ps) 
      | PRef _ n <- getTm p 
        = do ps' <- getWParams ps
             ctxt <- getContext
             case lookupP Nothing n ctxt of
                [] -> return (pimp n (PRef fc n) : ps')
                _ -> return ps'
    getWParams (_ : ps) = getWParams ps

    decorate ns iname (UN n) = NS (UN ('!':n)) ns
    decorate ns iname (NS (UN n) s) = NS (UN ('!':n)) ns

    mkTyDecl (n, op, t, _) = PTy "" syn fc op n t

    conbind (ty : ns) x = PPi constraint (MN 0 "c") ty (conbind ns x)
    conbind [] x = x

    coninsert cs (PPi p@(Imp _ _ _) n t sc) = PPi p n t (coninsert cs sc)
    coninsert cs sc = conbind cs sc

    insertDefaults :: IState -> Name ->
                      [(Name, (Name, PDecl))] -> [String] -> 
                      [PDecl] -> [PDecl]
    insertDefaults i iname [] ns ds = ds
    insertDefaults i iname ((n,(dn, clauses)) : defs) ns ds 
       = insertDefaults i iname defs ns (insertDef i n dn clauses ns iname ds)

    insertDef i meth def clauses ns iname decls
        | null $ filter (clauseFor meth iname ns) decls
            = let newd = expandParamsD False i (\n -> meth) [] [def] clauses in
                  -- trace (show newd) $ 
                  decls ++ [newd]
        | otherwise = decls

    warnMissing decls ns iname meth
        | null $ filter (clauseFor meth iname ns) decls
            = iWarn fc $ "method " ++ show meth ++ " not defined"
        | otherwise = return ()

    checkInClass ns meth
        | not (null (filter (eqRoot meth) ns)) = return ()
        | otherwise = tclift $ tfail (At fc (Msg $ 
                                show meth ++ " not a method of class " ++ show n))

    eqRoot x y = nsroot x == nsroot y

    clauseFor m iname ns (PClauses _ _ m' _) 
       = decorate ns iname m == decorate ns iname m'
    clauseFor m iname ns _ = False

decorateid decorate (PTy doc s f o n t) = PTy doc s f o (decorate n) t
decorateid decorate (PClauses f o n cs) 
   = PClauses f o (decorate n) (map dc cs)
    where dc (PClause fc n t as w ds) = PClause fc (decorate n) (dappname t) as w ds
          dc (PWith   fc n t as w ds) = PWith   fc (decorate n) (dappname t) as w 
                                              (map (decorateid decorate) ds)
          dappname (PApp fc (PRef fc' n) as) = PApp fc (PRef fc' (decorate n)) as
          dappname t = t


pbinds (Bind n (PVar t) sc) = do attack; patbind n 
                                 pbinds sc
pbinds tm = return ()

pbty (Bind n (PVar t) sc) tm = Bind n (PVTy t) (pbty sc tm)
pbty _ tm = tm

getPBtys (Bind n (PVar t) sc) = (n, t) : getPBtys sc
getPBtys _ = []

psolve (Bind n (PVar t) sc) = do solve; psolve sc
psolve tm = return ()

pvars ist (Bind n (PVar t) sc) = (n, delab ist t) : pvars ist sc
pvars ist _ = []

data ElabWhat = ETypes | EDefns | EAll
  deriving (Show, Eq)

elabDecls :: ElabInfo -> [PDecl] -> Idris ()
elabDecls info ds = do mapM_ (elabDecl EAll info) ds
--                       mapM_ (elabDecl EDefns info) ds

elabDecl :: ElabWhat -> ElabInfo -> PDecl -> Idris ()
elabDecl what info d 
    = idrisCatch (elabDecl' what info d) 
                 (\e -> do let msg = show e
                           setErrLine (getErrLine msg)
                           iputStrLn msg)

elabDecl' _ info (PFix _ _ _)
     = return () -- nothing to elaborate
elabDecl' _ info (PSyntax _ p) 
     = return () -- nothing to elaborate
elabDecl' what info (PTy doc s f o n ty)    
  | what /= EDefns
    = do iLOG $ "Elaborating type decl " ++ show n ++ show o
         elabType info s doc f o n ty
elabDecl' what info (PPostulate doc s f o n ty)    
  | what /= EDefns
    = do iLOG $ "Elaborating postulate " ++ show n ++ show o
         elabPostulate info s doc f o n ty
elabDecl' what info (PData doc s f co d)    
  | what /= ETypes
    = do iLOG $ "Elaborating " ++ show (d_name d)
         elabData info s doc f co d
  | otherwise 
    = do iLOG $ "Elaborating [type of] " ++ show (d_name d)
         elabData info s doc f co (PLaterdecl (d_name d) (d_tcon d))
elabDecl' what info d@(PClauses f o n ps) 
  | what /= ETypes
    = do iLOG $ "Elaborating clause " ++ show n
         i <- get -- get the type options too
         let o' = case lookupCtxt Nothing n (idris_flags i) of
                    [fs] -> fs
                    [] -> []
         elabClauses info f (o ++ o') n ps
elabDecl' what info (PMutual f ps) 
    = do mapM_ (elabDecl ETypes info) ps
         mapM_ (elabDecl EDefns info) ps
elabDecl' what info (PParams f ns ps) 
    = do i <- get
         iLOG $ "Expanding params block with " ++ show ns ++ " decls " ++
                show (concatMap declared ps)
         let nblock = pblock i
         mapM_ (elabDecl' what info) nblock 
  where
    pinfo = let ds = concatMap declared ps
                newps = params info ++ ns
                dsParams = map (\n -> (n, map fst newps)) ds
                newb = addAlist dsParams (inblock info) in 
                info { params = newps,
                       inblock = newb }
    pblock i = map (expandParamsD False i id ns 
                      (concatMap declared ps)) ps

elabDecl' what info (PNamespace n ps) = mapM_ (elabDecl' what ninfo) ps
  where
    ninfo = case namespace info of
                Nothing -> info { namespace = Just [n] }
                Just ns -> info { namespace = Just (n:ns) } 
elabDecl' what info (PClass doc s f cs n ps ds) 
  | what /= EDefns
    = do iLOG $ "Elaborating class " ++ show n
         elabClass info s doc f cs n ps ds
elabDecl' what info (PInstance s f cs n ps t expn ds) 
  | what /= ETypes
    = do iLOG $ "Elaborating instance " ++ show n
         elabInstance info s f cs n ps t expn ds
elabDecl' what info (PRecord doc s f tyn ty cdoc cn cty)
  | what /= EDefns
    = do iLOG $ "Elaborating record " ++ show tyn
         elabRecord info s doc f tyn ty cdoc cn cty
elabDecl' _ info (PDSL n dsl)
    = do i <- get
         put (i { idris_dsls = addDef n dsl (idris_dsls i) }) 
         addIBC (IBCDSL n)
elabDecl' what info (PDirective i) 
  | what /= EDefns = i
elabDecl' _ _ _ = return () -- skipped this time 

elabCaseBlock info d@(PClauses f o n ps) 
        = do addIBC (IBCDef n)
--              iputStrLn $ "CASE BLOCK: " ++ show (n, d)
             elabDecl' EAll info d 

-- elabDecl' info (PImport i) = loadModule i

-- Check that the result of type checking matches what the programmer wrote
-- (i.e. - if we inferred any arguments that the user provided, make sure
-- they are the same!)

checkInferred :: FC -> PTerm -> PTerm -> Idris ()
checkInferred fc inf user =
     do logLvl 6 $ "Checked to\n" ++ showImp True inf ++ "\n\nFROM\n\n" ++
                                     showImp True user
        logLvl 10 $ "Checking match"
        i <- get
        tclift $ case matchClause' True i user inf of 
            Right vs -> return ()
            Left (x, y) -> tfail $ At fc 
                                    (Msg $ "The type-checked term and given term do not match: "
                                           ++ show x ++ " and " ++ show y)
        logLvl 10 $ "Checked match"
--                           ++ "\n" ++ showImp True inf ++ "\n" ++ showImp True user)

-- Return whether inferred term is different from given term
-- (as above, but return a Bool)

inferredDiff :: FC -> PTerm -> PTerm -> Idris Bool
inferredDiff fc inf user =
     do i <- get
        logLvl 6 $ "Checked to\n" ++ showImp True inf ++ "\n" ++
                                     showImp True user
        tclift $ case matchClause' True i user inf of 
            Right vs -> return False
            Left (x, y) -> return True


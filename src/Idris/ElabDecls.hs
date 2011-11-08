{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.ElabDecls where

import Idris.AbsSyntax
import Idris.Error
import Idris.Delaborate
import Idris.Imports
import Paths_idris

import Core.TT
import Core.Elaborate hiding (Tactic(..))
import Core.Evaluate
import Core.Typecheck
import Core.CaseTree

import Control.Monad
import Control.Monad.State
import Data.List
import Debug.Trace

-- Data to pass to recursively called elaborators; e.g. for where blocks,
-- paramaterised declarations, etc.

data ElabInfo = EInfo { params :: [(Name, PTerm)],
                        inblock :: Ctxt [Name], -- names in the block, and their params
                        liftname :: Name -> Name }

toplevel = EInfo [] emptyContext id

checkDef ns = do ctxt <- getContext
                 mapM (\(n, t) -> do (t', _) <- tclift $ recheck ctxt [] t
                                     return (n, t')) ns

elabType :: ElabInfo -> SyntaxInfo -> FC -> Name -> PTerm -> Idris ()
elabType info syn fc n ty' = {- let ty' = piBind (params info) ty_in 
                                      n  = liftname info n_in in    -}
      do checkUndefined fc n
         ctxt <- getContext
         i <- get
         ty' <- implicit syn n ty'
         let ty = addImpl i ty'
         logLvl 2 $ show n ++ " type " ++ showImp True ty
         ((ty', defer), log) <- tclift $ elaborate ctxt n (Set 0) 
                                         (erun fc (build i info False ty))
         (cty, _)   <- tclift $ recheck ctxt [] ty'
         logLvl 2 $ "---> " ++ show cty
         let nty = normalise ctxt [] cty
         ds <- checkDef ((n, nty):defer)
         addDeferred ds

elabData :: ElabInfo -> SyntaxInfo -> FC -> PData -> Idris ()
elabData info syn fc (PDatadecl n t_in dcons)
    = do iLOG (show fc)
         checkUndefined fc n
         ctxt <- getContext
         i <- get
         t_in <- implicit syn n t_in
         let t = addImpl i t_in
         ((t', defer), log) <- tclift $ elaborate ctxt n (Set 0) 
                                        (erun fc (build i info False t))
         def' <- checkDef defer
         addDeferred def'
         (cty, _)  <- tclift $ recheck ctxt [] t'
         logLvl 2 $ "---> " ++ show cty
         updateContext (addTyDecl n cty) -- temporary, to check cons
         cons <- mapM (elabCon info syn) dcons
         ttag <- getName
         setContext (addDatatype (Data n ttag cty cons) ctxt)

elabCon :: ElabInfo -> SyntaxInfo -> (Name, PTerm, FC) -> Idris (Name, Type)
elabCon info syn (n, t_in, fc)
    = do checkUndefined fc n
         ctxt <- getContext
         i <- get
         t_in <- implicit syn n t_in
         let t = addImpl i t_in
         logLvl 2 $ show fc ++ ":Constructor " ++ show n ++ " : " ++ showImp True t
         ((t', defer), log) <- tclift $ elaborate ctxt n (Set 0) 
                                        (erun fc (build i info False t))
         logLvl 2 $ "Rechecking " ++ show t'
         def' <- checkDef defer
         addDeferred def'
         (cty, _)  <- tclift $ recheck ctxt [] t'
         logLvl 2 $ "---> " ++ show n ++ " : " ++ show cty
         return (n, cty)

elabClauses :: ElabInfo -> FC -> Name -> [PClause] -> Idris ()
elabClauses info fc n_in cs = let n = liftname info n_in in  
      do solveDeferred n
         pats <- mapM (elabClause info fc) cs
         logLvl 3 (showSep "\n" (map (\ (l,r) -> 
                                        show l ++ " = " ++ 
                                        show r) pats))
         ist <- get
         let tcase = opt_typecase (idris_options ist)
         let tree = simpleCase tcase (map debind pats)
         logLvl 3 (show tree)
         ctxt <- getContext
         case lookupTy n ctxt of
             Just ty -> updateContext (addCasedef n tcase (map debind pats) ty)
             Nothing -> return ()
  where
    debind (x, y) = (depat x, depat y)
    depat (Bind n (PVar t) sc) = depat (instantiate (P Bound n t) sc)
    depat x = x

elabVal :: ElabInfo -> Bool -> PTerm -> Idris (Term, Type)
elabVal info aspat tm_in
   = do ctxt <- getContext
        i <- get
        let tm = addImpl i tm_in
        logLvl 10 (showImp True tm)
        ((tm', defer), _) <- tclift $ elaborate ctxt (MN 0 "val") infP
                                      (build i info aspat (infTerm tm))
        logLvl 3 ("Value: " ++ show tm')
        let vtm = getInferTerm tm'
        logLvl 2 (show vtm)
        tclift $ recheck ctxt [] vtm

elabClause :: ElabInfo -> FC -> PClause -> Idris (Term, Term)
elabClause info fc (PClause fname lhs_in withs rhs_in whereblock) 
   = do ctxt <- getContext
        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        i <- get
        let lhs = addImpl i lhs_in
        logLvl 5 ("LHS: " ++ showImp True lhs)
        ((lhs', dlhs), _) <- tclift $ elaborate ctxt (MN 0 "patLHS") infP
                                      (erun fc (build i info True (infTerm lhs)))
        let lhs_tm = orderPats (getInferTerm lhs')
        let lhs_ty = getInferType lhs'
        logLvl 3 (show lhs_tm)
        (clhs, clhsty) <- tclift $ recheck ctxt [] lhs_tm
        logLvl 5 ("Checked " ++ show clhs)
        -- Elaborate where block
        ist <- getIState
        windex <- getName
        let winfo = pinfo (pvars ist lhs_tm) whereblock windex
        let decls = concatMap declared whereblock
        let newargs = pvars ist lhs_tm
        let newargs' = updateNewargs (namesIn ist rhs_in) (zip newargs [0..])
        let wb = map (expandParamsD decorate newargs' decls) whereblock
        logLvl 5 $ show wb
        mapM_ (elabDecl' info) wb
        -- Now build the RHS, using the type of the LHS as the goal.
        i <- get -- new implicits from where block
        logLvl 5 (showImp True (expandParams decorate newargs decls rhs_in))
        let rhs = addImpl i (expandParams decorate newargs decls rhs_in)
                        -- TODO: but don't do names in scope
        logLvl 2 (showImp True rhs)
        ctxt <- getContext -- new context with where block added
        ((rhs', defer), _) <- 
           tclift $ elaborate ctxt (MN 0 "patRHS") clhsty
                    (do pbinds lhs_tm
                        (_, _) <- erun fc (build i info False rhs)
                        psolve lhs_tm
                        tt <- get_term
                        return $ runState (collectDeferred tt) [])
        logLvl 2 $ "---> " ++ show rhs'
        when (not (null defer)) $ iLOG $ "DEFERRED " ++ show defer
        def' <- checkDef defer
        addDeferred def'
        ctxt <- getContext
        (crhs, crhsty) <- tclift $ recheck ctxt [] rhs'
        return (clhs, crhs)
  where
    updateNewargs nm [] = []
    updateNewargs nm (((a, t), i):as)
        | a `elem` nm = (a, t) : updateNewargs nm as
        | otherwise = (MN i (show fname ++ "_u"), t) : updateNewargs nm as

    decorate x = UN [show fname ++ "#" ++ show x]
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

elabClause info fc (PWith fname lhs_in withs wval_in withblock) 
   = do ctxt <- getContext
        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        i <- get
        let lhs = addImpl i lhs_in
        logLvl 5 ("LHS: " ++ showImp True lhs)
        ((lhs', dlhs), _) <- tclift $ elaborate ctxt (MN 0 "patLHS") infP
                                      (erun fc (build i info True (infTerm lhs)))
        let lhs_tm = orderPats (getInferTerm lhs')
        let lhs_ty = getInferType lhs'
        let ret_ty = getRetTy lhs_ty
        logLvl 3 (show lhs_tm)
        (clhs, clhsty) <- tclift $ recheck ctxt [] lhs_tm
        logLvl 5 ("Checked " ++ show clhs)
        let bargs = getPBtys lhs_tm
        let wval = addImpl i wval_in
        logLvl 5 ("Checking " ++ showImp True wval)
        -- Elaborate wval in this context
        ((wval', defer), _) <- 
            tclift $ elaborate ctxt (MN 0 "withRHS") 
                        (bindTyArgs PVTy bargs infP)
                        (do pbinds lhs_tm
                            -- TODO: may want where here - see winfo abpve
                            (_', d) <- erun fc (build i info False (infTerm wval))
                            psolve lhs_tm
                            tt <- get_term
                            return (tt, d))
        def' <- checkDef defer
        addDeferred def'
        (cwval, cwvalty) <- tclift $ recheck ctxt [] (getInferTerm wval')
        logLvl 3 ("With type " ++ show cwvalty ++ "\nRet type " ++ show ret_ty)
        windex <- getName
        -- build a type declaration for the new function:
        -- (ps : Xs) -> (withval : cwvalty) -> ret_ty 
        let wtype = bindTyArgs Pi (bargs ++ [(MN 0 "warg", getRetTy cwvalty)]) ret_ty
        logLvl 3 ("New function type " ++ show wtype)
        let wname = MN windex (show fname)
        let imps = getImps wtype -- add to implicits context
        put (i { idris_implicits = addDef wname imps (idris_implicits i) })
        def' <- checkDef [(wname, wtype)]
        addDeferred def'

        -- in the subdecls, lhs becomes:
        --         fname  pats | wpat [rest]
        --    ==>  fname' ps   wpat [rest], match pats against toplevel for ps
        wb <- mapM (mkAuxC wname lhs (map fst bargs)) withblock
        logLvl 5 ("with block " ++ show wb)
        mapM_ (elabDecl info) wb

        -- rhs becomes: fname' ps wval
        let rhs = PApp fc (PRef fc wname) (map (pexp . (PRef fc) . fst) bargs ++ 
                                                [pexp wval])
        logLvl 3 ("New RHS " ++ show rhs)
        ctxt <- getContext -- New context with block added
        i <- get
        ((rhs', defer), _) <-
           tclift $ elaborate ctxt (MN 0 "wpatRHS") clhsty
                    (do pbinds lhs_tm
                        (_, d) <- erun fc (build i info False rhs)
                        psolve lhs_tm
                        tt <- get_term
                        return (tt, d))
        def' <- checkDef defer
        addDeferred def'
        (crhs, crhsty) <- tclift $ recheck ctxt [] rhs'
        return (clhs, crhs)
  where
    getImps (Bind n (Pi _) t) = pexp Placeholder : getImps t
    getImps _ = []

    mkAuxC wname lhs ns (PClauses fc n cs)
        | n == fname = do cs' <- mapM (mkAux wname lhs ns) cs
                          return $ PClauses fc wname cs'
        | otherwise = fail $ "with clause uses wrong function name " ++ show n
    mkAuxC wname lhs ns d = return $ d

    mkAux wname toplhs ns (PClause n tm_in (w:ws) rhs wheres)
        = do i <- get
             let tm = addImpl i tm_in
             logLvl 2 ("Matching " ++ showImp True tm ++ " against " ++ 
                                      showImp True toplhs)
             case matchClause toplhs tm of
                Nothing -> fail "with clause does not match top level"
                Just mvars -> do logLvl 3 ("Match vars : " ++ show mvars)
                                 lhs <- updateLHS n wname mvars ns tm w
                                 return $ PClause wname lhs ws rhs wheres
    mkAux wname toplhs ns (PWith n tm_in (w:ws) wval wheres)
        = do i <- get
             let tm = addImpl i tm_in
             logLvl 2 ("Matching " ++ showImp True tm ++ " against " ++ 
                                      showImp True toplhs)
             case matchClause toplhs tm of
                Nothing -> fail "with clause does not match top level"
                Just mvars -> do lhs <- updateLHS n wname mvars ns tm w
                                 return $ PWith wname lhs ws wval wheres
        
    updateLHS n wname mvars ns (PApp fc (PRef fc' n') args) w
        = return $ substMatches mvars $ 
                PApp fc (PRef fc' wname) (map (pexp . (PRef fc')) ns ++ [pexp w])
    updateLHS n wname mvars ns tm w = fail $ "Not implemented " ++ show tm 

elabClass :: ElabInfo -> SyntaxInfo -> 
             FC -> [PTerm] -> 
             Name -> [(Name, PTerm)] -> [PDecl] -> Idris ()
elabClass info syn fc constraints tn ps ds 
    = do let cn = UN ["instance" ++ show tn] -- MN 0 ("instance" ++ show tn)
         let tty = pibind ps PSet
         let constraint = PApp fc (PRef fc tn)
                                  (map (pexp . PRef fc) (map fst ps))
         -- build data declaration
         ims <- mapM tdecl ds
         let (methods, imethods) = unzip ims
         let cty = impbind ps $ conbind constraints $ pibind methods constraint
         let cons = [(cn, cty, fc)]
         let ddecl = PData syn fc (PDatadecl tn tty cons)
         elabDecl info ddecl
         -- for each method, build a top level function
         let usyn = syn { using = ps ++ using syn }
         fns <- mapM (tfun cn constraint usyn (map fst imethods)) imethods
         mapM_ (elabDecl info) (concat fns)
         i <- get
         put (i { idris_classes = addDef tn (CI cn imethods (map fst ps)) 
                                            (idris_classes i) })
  where
    pibind [] x = x
    pibind ((n, ty): ns) x = PPi expl n ty (pibind ns x) 
    impbind [] x = x
    impbind ((n, ty): ns) x = PPi impl n ty (impbind ns x) 
    conbind (ty : ns) x = PPi constraint (MN 0 "c") ty (conbind ns x)
    conbind [] x = x

    tdecl (PTy syn _ n t) = do t' <- implicit syn n t
                               return ( (n, (toExp (map fst ps) Exp t')),
                                        (n, (toExp (map fst ps) Imp t')) )
    tdecl (PClauses _ _ _) = fail "No default definitions allowed yet"
    tdecl _ = fail "Not allowed in a class declaration"

    tfun cn c syn all (m, ty) 
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
             return [PTy syn fc m ty',
                     PClauses fc m [PClause m lhs [] rhs []]]

    getMArgs (PPi (Imp _ _) n ty sc) = False : getMArgs sc
    getMArgs (PPi (Exp _ _) n ty sc) = True  : getMArgs sc
    getMArgs _ = []

    getMeth (m:ms) (a:as) x | x == a = PRef fc m
                            | otherwise = getMeth ms as x

    lhsArgs (True : xs) (n : ns) = pexp (PRef fc n) : lhsArgs xs ns 
    lhsArgs (False : xs) ns = lhsArgs xs ns 
    lhsArgs [] _ = []

    rhsArgs (True : xs) (n : ns) = pexp (PRef fc n) : rhsArgs xs ns 
    rhsArgs (False : xs) ns = pexp Placeholder : rhsArgs xs ns 
    rhsArgs [] _ = []

    insertConstraint c (PPi p@(Imp _ _) n ty sc)
                          = PPi p n ty (insertConstraint c sc)
    insertConstraint c sc = PPi constraint (MN 0 "c") c sc

    -- make arguments explicit and don't bind class parameters
    toExp ns e (PPi (Imp l s) n ty sc)
        | n `elem` ns = toExp ns e sc
        | otherwise = PPi (e l s) n ty (toExp ns e sc)
    toExp ns e (PPi p n ty sc) = PPi p n ty (toExp ns e sc)
    toExp ns e sc = sc

elabInstance :: ElabInfo -> SyntaxInfo -> 
                FC -> [PTerm] -> Name -> 
                [PTerm] -> PTerm -> [PDecl] -> Idris ()
elabInstance info syn fc cs n ps t ds
    = do i <- get 
         ci <- case lookupCtxt n (idris_classes i) of
                    Just c -> return c
                    Nothing -> fail $ show n ++ " is not a type class"
         let iname = UN ['@':show n ++ "$" ++ show ps]
         elabType info syn fc iname t
         let ips = zip (class_params ci) ps
         let mtys = map (\ (n, t) -> (decorate n, coninsert cs $ substMatches ips t)) 
                        (class_methods ci)
         logLvl 3 (show (mtys, ips))
         let wb = map mkTyDecl mtys ++ map decorateid ds
         let lhs = PRef fc iname
         let rhs = PApp fc (PRef fc (instanceName ci))
                           (map (pexp . mkMethApp) mtys)
         let idecl = PClauses fc iname [PClause iname lhs [] rhs wb]
         iLOG (show idecl)
         elabDecl info idecl
  where
    mkMethApp (n, ty) = lamBind 0 ty (papp fc (PRef fc n) (methArgs 0 ty))
    lamBind i (PPi (Constraint _ _) _ _ sc) sc' = lamBind i sc sc'
    lamBind i (PPi _ n ty sc) sc' = PLam (MN i "meth") Placeholder (lamBind (i+1) sc sc')
    lamBind i _ sc = sc
    methArgs i (PPi (Imp _ _) n ty sc) 
        = PImp 0 False n (PRef fc (MN i "meth")) : methArgs (i+1) sc
    methArgs i (PPi (Exp _ _) n ty sc) 
        = PExp 0 False (PRef fc (MN i "meth")) : methArgs (i+1) sc
    methArgs i (PPi (Constraint _ _) n ty sc) 
        = methArgs i sc
    methArgs i _ = []

    papp fc f [] = f
    papp fc f as = PApp fc f as
    decorate (UN (n:ns)) = UN (('!':n) : ns)
    decorateid (PTy s f n t) = PTy s f (decorate n) t
    decorateid (PClauses f n cs) = PClauses f (decorate n) (map dc cs)
      where dc (PClause n t as w ds) = PClause (decorate n) (dappname t) as w ds
            dc (PWith   n t as w ds) = PWith   (decorate n) (dappname t) as w ds
            dappname (PApp fc (PRef fc' n) as) = PApp fc (PRef fc' (decorate n)) as
            dappname t = t
    mkTyDecl (n, t) = PTy syn fc n t

    conbind (ty : ns) x = PPi constraint (MN 0 "c") ty (conbind ns x)
    conbind [] x = x

    coninsert cs (PPi p@(Imp _ _) n t sc) = PPi p n t (coninsert cs sc)
    coninsert cs sc = conbind cs sc

pbinds (Bind n (PVar t) sc) = do attack; patbind n 
                                 pbinds sc
pbinds tm = return ()

pbty (Bind n (PVar t) sc) tm = Bind n (PVTy t) (pbty sc tm)
pbty _ tm = tm

getPBtys (Bind n (PVar t) sc) = (n, t) : getPBtys sc
getPBtys _ = []

getRetTy (Bind n (PVar _) sc) = getRetTy sc
getRetTy (Bind n (PVTy _) sc) = getRetTy sc
getRetTy (Bind n (Pi _) sc)   = getRetTy sc
getRetTy sc = sc

psolve (Bind n (PVar t) sc) = do solve; psolve sc
psolve tm = return ()

pvars ist (Bind n (PVar t) sc) = (n, delab ist t) : pvars ist sc
pvars ist _ = []

-- TODO: Also build a 'binary' version of each declaration for fast reloading

elabDecl :: ElabInfo -> PDecl -> Idris ()
elabDecl info d = idrisCatch (elabDecl' info d) 
                             (\e -> do let msg = report e
                                       setErrLine (getErrLine msg)
                                       iputStrLn msg)

elabDecl' info (PFix _ _ _)      = return () -- nothing to elaborate
elabDecl' info (PSyntax _ p) = return () -- nothing to elaborate
elabDecl' info (PTy s f n ty)    = do iLOG $ "Elaborating type decl " ++ show n
                                      elabType info s f n ty
elabDecl' info (PData s f d)     = do iLOG $ "Elaborating " ++ show (d_name d)
                                      elabData info s f d
elabDecl' info d@(PClauses f n ps) = do iLOG $ "Elaborating clause " ++ show n
                                        elabClauses info f n ps
elabDecl' info (PParams f ns ps) = mapM_ (elabDecl' pinfo) ps
  where
    pinfo = let ds = concatMap declared ps
                newps = params info ++ ns
                dsParams = map (\n -> (n, map fst newps)) ds
                newb = addAlist dsParams (inblock info) in 
                info { params = newps,
                       inblock = newb }
elabDecl' info (PClass s f cs n ps ds) = do iLOG $ "Elaborating class " ++ show n
                                            elabClass info s f cs n ps ds
elabDecl' info (PInstance s f cs n ps t ds) 
    = do iLOG $ "Elaborating instance " ++ show n
         elabInstance info s f cs n ps t ds


-- elabDecl' info (PImport i) = loadModule i


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

    elab' PSet           = do fill (RSet 0); solve
    elab' (PConstant c)  = do apply (RConstant c) []; solve
    elab' (PQuote r)     = do fill r; solve
    elab' (PTrue fc)     = try (elab' (PRef fc unitCon))
                               (elab' (PRef fc unitTy))
    elab' (PFalse fc)    = elab' (PRef fc falseTy)
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
    elab' (PDPair fc l@(PRef _ n) r)
                          = try (elab' (PApp fc (PRef fc sigmaTy)
                                        [pexp Placeholder,
                                         pexp (PLam n Placeholder r)]))
                                (elab' (PApp fc (PRef fc existsCon)
                                             [pimp (MN 0 "a") Placeholder,
                                              pimp (MN 0 "P") Placeholder,
                                              pexp l, pexp r]))
    elab' (PDPair fc l r) = elab' (PApp fc (PRef fc existsCon)
                                            [pimp (MN 0 "a") Placeholder,
                                             pimp (MN 0 "P") Placeholder,
                                             pexp l, pexp r])
    elab' (PRef fc n) | pattern && not (inparamBlock n)
                         = erun fc $ 
                            try (do apply (Var n) []; solve)
                                (patvar n)
      where inparamBlock n = case lookupCtxt n (inblock info) of
                                Nothing -> False
                                _ -> True
    elab' (PRef fc n) = erun fc $ do apply (Var n) []; solve
    elab' (PLam n Placeholder sc)
                         = do attack; intro (Just n); elabE sc; solve
    elab' (PPi _ n Placeholder sc)
                         = do attack; arg n (MN 0 "ty"); elabE sc; solve
    elab' (PPi _ n ty sc) 
          = do attack; tyn <- unique_hole (MN 0 "ty")
               claim tyn (RSet 0)
               forall n (Var tyn)
               focus tyn
               elabE ty
               elabE sc
               solve
    elab' (PLet n Placeholder val sc)
          = do attack; -- (h:_) <- get_holes
               tyn <- unique_hole (MN 0 "letty")
               -- start_unify h
               claim tyn (RSet 0)
               valn <- unique_hole (MN 0 "letval")
               claim valn (Var tyn)
               letbind n (Var tyn) (Var valn)  
               focus valn
               elabE val
               elabE sc
               -- end_unify
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
                                resolveTC 10 ist) (ivs' \\ ivs) 
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
    elab' (PMetavar n) = do attack; defer n; solve
    elab' (PProof ts) = do mapM_ (runTac True ist) ts
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
          = do elabArg n (PApp bi (PRef bi (UN ["lazy"]))
                               [pimp (UN ["a"]) Placeholder,
                                pexp t]); 
        | otherwise = elabArg n t
      where elabArg n t = if r
                            then try (do focus n; elabE t; elabArgs failed r ns args) 
                                     (elabArgs ((n,(lazy, t)):failed) r ns args)
                            else do focus n; elabE t; elabArgs failed r ns args
   
trivial :: IState -> Elab ()
trivial ist = try (elab ist toplevel False (PRefl (FC "prf" 0)))
                  (do env <- get_env
                      tryAll (map fst env))
      where
        tryAll []     = fail "No trivial solution"
        tryAll (x:xs) = try (elab ist toplevel False (PRef (FC "prf" 0) x))
                            (tryAll xs)

resolveTC :: Int -> IState -> Elab ()
resolveTC depth ist 
              = do t <- goal
                   tm <- get_term
                   try (trivial ist)
                       (blunderbuss t (map fst (toAlist (tt_ctxt ist))))
  where
    blunderbuss t [] = fail $ "Can't resolve type class " ++ show t
    blunderbuss t (n:ns) | tcname n = try (resolve n depth)
                                          (blunderbuss t ns)
                         | otherwise = blunderbuss t ns
    tcname (UN (('@':_) : _)) = True
    tcname _ = False

    resolve n depth
       | depth == 0 = fail $ "Can't resolve type class"
       | otherwise 
              = do t <- goal
                   let imps = case lookupCtxt n (idris_implicits ist) of
                                Nothing -> []
                                Just args -> map isImp args
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
    runT (Refine fn [])   = do let imps = case lookupCtxt fn (idris_implicits ist) of
                                            Nothing -> []
                                            Just args -> map isImp args
                               ns <- apply (Var fn) imps
                               when autoSolve solveAll
       where isImp (PImp _ _ _ _) = True
             isImp _ = False
    runT (Refine fn imps) = do ns <- apply (Var fn) imps
                               when autoSolve solveAll
    runT (Rewrite tm) -- to elaborate tm, let bind it, then rewrite by that
              = do attack; -- (h:_) <- get_holes
                   tyn <- unique_hole (MN 0 "rty")
                   -- start_unify h
                   claim tyn (RSet 0)
                   valn <- unique_hole (MN 0 "rval")
                   claim valn (Var tyn)
                   letn <- unique_hole (MN 0 "rewrite_rule")
                   letbind letn (Var tyn) (Var valn)  
                   focus valn
                   elab ist toplevel False tm
                   rewrite (Var letn)
                   when autoSolve solveAll
    runT Compute = compute
    runT Trivial = do trivial ist; when autoSolve solveAll
    runT (Focus n) = focus n
    runT Solve = solve
    runT x = fail $ "Not implemented " ++ show x

solveAll = try (do solve; solveAll) (return ())

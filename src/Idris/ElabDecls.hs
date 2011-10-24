{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.ElabDecls where

import Idris.AbsSyntax
import Idris.Error
import Idris.Delaborate
import Idris.Imports
import Paths_miniidris

import Core.TT
import Core.Elaborate
import Core.Evaluate
import Core.Typecheck
import Core.CaseTree

import Control.Monad
import Control.Monad.State
import Debug.Trace

-- Data to pass to recursively called elaborators; e.g. for where blocks,
-- paramaterised declarations, etc.

data ElabInfo = EInfo { params :: [(Name, PTerm)],
                        inblock :: Ctxt [Name], -- names in the block, and their params
                        liftname :: Name -> Name }

toplevel = EInfo [] emptyContext id

elabType :: ElabInfo -> FC -> Name -> PTerm -> Idris ()
elabType info fc n_in ty_in = let ty = piBind (params info) ty_in 
                                  n  = liftname info n_in in    
      do checkUndefined fc n
         ctxt <- getContext
         logLvl 2 $ "Type " ++ showImp True ty
         ((ty', defer), log) <- tclift $ elaborate ctxt n (Set 0) 
                                         (erun fc (build info False ty))
         (cty, _)   <- tclift $ recheck ctxt [] ty'
         logLvl 2 $ "---> " ++ show cty
         let nty = normalise ctxt [] cty
         addDeferred ((n, nty):defer)

elabData :: ElabInfo -> FC -> PData -> Idris ()
elabData info fc (PDatadecl n t dcons)
    = do iLOG (show fc)
         checkUndefined fc n
         ctxt <- getContext
         ((t', defer), log) <- tclift $ elaborate ctxt n (Set 0) 
                                        (erun fc (build info False t))
         addDeferred defer
         (cty, _)  <- tclift $ recheck ctxt [] t'
         logLvl 2 $ "---> " ++ show cty
         updateContext (addTyDecl n cty) -- temporary, to check cons
         cons <- mapM (elabCon info) dcons
         setContext (addDatatype (Data n cty cons) ctxt)

elabCon :: ElabInfo -> (Name, PTerm, FC) -> Idris (Name, Type)
elabCon info (n, t, fc)
    = do checkUndefined fc n
         ctxt <- getContext
         logLvl 2 $ show fc ++ ":Constructor " ++ show n ++ " : " ++ showImp True t
         ((t', defer), log) <- tclift $ elaborate ctxt n (Set 0) 
                                        (erun fc (build info False t))
         logLvl 2 $ "Rechecking " ++ show t'
         addDeferred defer
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
         let tree = simpleCase (map debind pats)
         logLvl 3 (show tree)
         ctxt <- getContext
         case lookupTy n ctxt of
             Just ty -> updateContext (addCasedef n (map debind pats) ty)
             Nothing -> return ()
  where
    debind (x, y) = (depat x, depat y)
    depat (Bind n (PVar t) sc) = depat (instantiate (P Bound n t) sc)
    depat x = x

elabVal :: ElabInfo -> PTerm -> Idris (Term, Type)
elabVal info tm
   = do ctxt <- getContext
        logLvl 10 (showImp True tm)
        ((tm', defer), _) <- tclift $ elaborate ctxt (MN 0 "val") infP
                                      (build info True (infTerm tm))
        logLvl 3 ("Value: " ++ show tm')
        let vtm = getInferTerm tm'
        logLvl 2 (show vtm)
        tclift $ recheck ctxt [] vtm

elabClause :: ElabInfo -> FC -> PClause -> Idris (Term, Term)
elabClause info fc (PClause fname lhs withs rhs whereblock) 
   = do ctxt <- getContext
        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        ((lhs', dlhs), _) <- tclift $ elaborate ctxt (MN 0 "patLHS") infP
                                      (erun fc (build info True (infTerm lhs)))
        let lhs_tm = getInferTerm lhs'
        let lhs_ty = getInferType lhs'
        logLvl 3 (show lhs_tm)
        (clhs, clhsty) <- tclift $ recheck ctxt [] lhs_tm
        logLvl 5 ("Checked " ++ show clhs)
        -- Elaborate where block
        ist <- getIState
        windex <- getName
        let winfo = pinfo (pvars ist lhs_tm) whereblock windex
        mapM_ (elabDecl' winfo) whereblock
        -- Now build the RHS, using the type of the LHS as the goal.
        logLvl 2 (showImp True rhs)
        ctxt <- getContext -- new context with where block added
        ((rhs', defer), _) <- 
           tclift $ elaborate ctxt (MN 0 "patRHS") clhsty
                    (do pbinds lhs_tm
                        (_, d) <- erun fc (build winfo False rhs)
                        psolve lhs_tm
                        tt <- get_term
                        return (tt, d))
        logLvl 2 $ "---> " ++ show rhs'
        when (not (null defer)) $ iLOG $ "DEFERRED " ++ show defer
        addDeferred defer
        (crhs, crhsty) <- tclift $ recheck ctxt [] rhs'
        return (clhs, crhs)
  where
    pinfo ns ps i 
          = let ds = concatMap declared ps
                newps = params info ++ ns
                dsParams = map (\n -> (n, map fst newps)) ds
                newb = addAlist dsParams (inblock info) 
                l = liftname info in
                info { params = newps,
                       inblock = newb,
                       liftname = (\n -> case lookupCtxt n newb of
                                           Nothing -> n
                                           _ -> MN i (show n)) . l
                    }

elabClause info fc (PWith fname lhs withs wval withblock) 
   = do ctxt <- getContext
        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        ((lhs', dlhs), _) <- tclift $ elaborate ctxt (MN 0 "patLHS") infP
                                      (erun fc (build info True (infTerm lhs)))
        let lhs_tm = getInferTerm lhs'
        let lhs_ty = getInferType lhs'
        let ret_ty = getRetTy lhs_ty
        logLvl 3 (show lhs_tm)
        (clhs, clhsty) <- tclift $ recheck ctxt [] lhs_tm
        logLvl 5 ("Checked " ++ show clhs)
        logLvl 5 ("Checking " ++ show wval)
        let bargs = getPBtys lhs_tm
        -- Elaborate wval in this context
        ((wval', defer), _) <- 
            tclift $ elaborate ctxt (MN 0 "withRHS") 
                        (bindTyArgs PVTy bargs infP)
                        (do pbinds lhs_tm
                            -- TODO: may want where here - see winfo abpve
                            (_', d) <- erun fc (build info False (infTerm wval))
                            psolve lhs_tm
                            tt <- get_term
                            return (tt, d))
        addDeferred defer
        (cwval, cwvalty) <- tclift $ recheck ctxt [] (getInferTerm wval')
        logLvl 3 ("With type " ++ show cwvalty ++ "\nRet type " ++ show ret_ty)
        windex <- getName
        -- build a type declaration for the new function:
        -- (ps : Xs) -> (withval : cwvalty) -> ret_ty 
        let wtype = bindTyArgs Pi (bargs ++ [(MN 0 "warg", getRetTy cwvalty)]) ret_ty
        logLvl 3 ("New function type " ++ show wtype)
        let wname = MN windex (show fname)
        addDeferred [(wname, wtype)]

        -- in the subdecls, lhs becomes:
        --         fname  pats | wpat [rest]
        --    ==>  fname' ps   wpat [rest]
        wb <- mapM (mkAuxC wname (map fst bargs)) withblock
        logLvl 5 ("with block " ++ show wb)
        mapM_ (elabDecl info) wb

        -- rhs becomes: fname' ps wval
        let rhs = PApp fc (PRef fc wname) (map (PExp . (PRef fc) . fst) bargs ++ 
                                                [PExp wval])
        logLvl 3 ("New RHS " ++ show rhs)
        ctxt <- getContext -- New context with block added
        ((rhs', defer), _) <-
           tclift $ elaborate ctxt (MN 0 "wpatRHS") clhsty
                    (do pbinds lhs_tm
                        (_, d) <- erun fc (build info False rhs)
                        psolve lhs_tm
                        tt <- get_term
                        return (tt, d))
        addDeferred defer
        (crhs, crhsty) <- tclift $ recheck ctxt [] rhs'
        return (clhs, crhs)
  where
    mkAuxC wname ns (PClauses fc n cs)
        | n == fname = do cs' <- mapM (mkAux wname ns) cs
                          return $ PClauses fc wname cs'
        | otherwise = fail $ "with clause uses wrong function name " ++ show n
    mkAuxC wname ns d = return $ d

    mkAux wname ns (PClause n tm (w:ws) rhs wheres)
        = do lhs <- updateLHS n wname ns tm w
             return $ PClause wname lhs ws rhs wheres
    mkAux wname ns (PWith n tm (w:ws) wval wheres)
        = do lhs <- updateLHS n wname ns tm w
             return $ PWith wname lhs ws wval wheres
        
    updateLHS n wname ns (PApp fc (PRef fc' n') args) w
        = return $ PApp fc (PRef fc' wname) 
                           (map (PExp . (PRef fc')) ns ++ [PExp w])
    updateLHS n wname ns tm w = fail $ "Not implemented " ++ show tm 

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
elabDecl info d = idrisCatch (elabDecl' info d) (\e -> iputStrLn (report e))

elabDecl' info (PFix _ _ _)      = return () -- nothing to elaborate
elabDecl' info (PSyntax _ p) = return () -- nothing to elaborate
elabDecl' info (PTy f n ty)      = do iLOG $ "Elaborating type decl " ++ show n
                                      elabType info f n ty
elabDecl' info (PData f d)       = do iLOG $ "Elaborating " ++ show (d_name d)
                                      elabData info f d
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
-- elabDecl' info (PImport i) = loadModule i


-- Using the elaborator, convert a term in raw syntax to a fully
-- elaborated, typechecked term.
--
-- If building a pattern match, we convert undeclared variables from
-- holes to pattern bindings.

-- Also find deferred names in the term and their types

build :: ElabInfo -> Bool -> PTerm -> Elab (Term, [(Name, Type)])
build info pattern tm = do elab info pattern tm
                           tt <- get_term
                           return $ runState (collectDeferred tt) []

elab :: ElabInfo -> Bool -> PTerm -> Elab ()
elab info pattern tm = do elab' tm
                          when pattern -- convert remaining holes to pattern vars
                               mkPat
  where
    isph arg = case getTm arg of
        Placeholder -> True
        _ -> False

    toElab arg = case getTm arg of
        Placeholder -> Nothing
        v -> Just (elab' v)

    mkPat = do hs <- get_holes
               case hs of
                  (h: hs) -> do patvar h; mkPat
                  [] -> return ()

    elab' PSet           = do fill (RSet 0); solve
    elab' (PConstant c)  = do apply (RConstant c) []; solve
    elab' (PQuote r)     = do fill r; solve
    elab' (PTrue fc)     = try (elab' (PRef fc unitCon))
                               (elab' (PRef fc unitTy))
    elab' (PFalse fc)    = elab' (PRef fc falseTy)
    elab' (PPair fc l r) = try (elab' (PApp fc (PRef fc pairTy)
                                            [PExp l,PExp r]))
                               (elab' (PApp fc (PRef fc pairCon)
                                            [PImp (MN 0 "A") Placeholder,
                                             PImp (MN 0 "B") Placeholder,
                                             PExp l, PExp r]))
    elab' (PRef fc n) | pattern && not (inparamBlock n)
                         = erun fc $ 
                            try (do apply (Var n) []; solve)
                                (patvar n)
      where inparamBlock n = case lookupCtxt n (inblock info) of
                                Nothing -> False
                                _ -> True
    elab' (PRef fc n)       
         | Just ps <- lookupCtxt n (inblock info) 
             = elab' (PApp fc (PRef fc n) [])
         | otherwise = erun fc $ do apply (Var n) []; solve
    elab' (PLam n Placeholder sc)
                         = do attack; intro n; elab' sc; solve
    elab' (PPi _ n Placeholder sc)
                         = do attack; arg n (MN 0 "ty"); elab' sc; solve
    elab' (PPi _ n ty sc) 
          = do attack; tyn <- unique_hole (MN 0 "ty")
               claim tyn (RSet 0)
               forall n (Var tyn)
               focus tyn
               elab' ty
               elab' sc
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
               elab' val
               elab' sc
               -- end_unify
               solve
    elab' (PApp fc (PRef _ f) args)
        | Just ps <- lookupCtxt f (inblock info) 
                    = erun fc $ 
                        elabApp (liftname info f) (map (PExp . (PRef fc)) ps ++ args)
        | otherwise = erun fc $ elabApp f args
      where elabApp f args
                  = try (do ns <- apply (Var f) (map isph args)
                            solve
                            elabArgs ns (map getTm args))
                        (do apply_elab f (map toElab args)
                            solve)
    elab' (PApp fc f [arg])
          = erun fc $ 
             do simple_app (elab' f) (elab' (getTm arg))
                solve
    elab' Placeholder = do (h : hs) <- get_holes
                           movelast h
    elab' (PMetavar n) = do attack; defer n; solve
    elab' (PElabError e) = fail e
    elab' x = fail $ "Not implemented " ++ show x

    elabArgs [] _ = return ()
    elabArgs (n:ns) (Placeholder : args) = elabArgs ns args
    elabArgs (n:ns) (t : args) = do focus n; elab' t; elabArgs ns args

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



{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.ElabDecls where

import Idris.AbsSyntax
import Idris.Error
import Idris.Delaborate

import Core.TT
import Core.Elaborate
import Core.Evaluate
import Core.Typecheck
import Core.CaseTree

import Control.Monad
import Debug.Trace

-- Data to pass to recursively called elaborators; e.g. for where blocks,
-- paramaterised declarations, etc.

data ElabInfo = EInfo { params :: [(Name, PTerm)],
                        liftname :: Name -> Name }

toplevel = EInfo [] id

elabType :: ElabInfo -> Name -> PTerm -> Idris ()
elabType info n ty 
    = do ctxt <- getContext
         logLvl 2 $ "Type " ++ showImp True ty
         (ty', log) <- tclift $ elaborate ctxt n (Set 0) (build False ty)
         (cty, _)   <- tclift $ recheck ctxt [] ty'
         logLvl 2 $ "---> " ++ show cty
         updateContext (addTyDecl n (normalise ctxt [] cty))

elabData :: ElabInfo -> PData -> Idris ()
elabData info (PDatadecl n t dcons)
    = do ctxt <- getContext
         (t', log) <- tclift $ elaborate ctxt n (Set 0) (build False t)
         (cty, _)  <- tclift $ recheck ctxt [] t'
         logLvl 2 $ "---> " ++ show cty
         updateContext (addTyDecl n cty) -- temporary, to check cons
         cons <- mapM (elabCon info) dcons
         setContext (addDatatype (Data n cty cons) ctxt)

elabCon :: ElabInfo -> (Name, PTerm) -> Idris (Name, Type)
elabCon info (n, t)
    = do ctxt <- getContext
         iLOG $ "Constructor " ++ show n ++ " : " ++ showImp True t
         (t', log) <- tclift $ elaborate ctxt n (Set 0) (build False t)
--          iLOG $ "Rechecking " ++ show t'
         (cty, _)  <- tclift $ recheck ctxt [] t'
         logLvl 2 $ "---> " ++ show n ++ " : " ++ show cty
         return (n, cty)

elabClauses :: ElabInfo -> Name -> [PClause] -> Idris ()
elabClauses info n cs 
    = do pats <- mapM (elabClause info) cs
         logLvl 3 (showSep "\n" (map (\ (l,r) -> 
                                        show l ++ " = " ++ 
                                        show r) pats))
         let tree = simpleCase (map debind pats)
         logLvl 3 (show tree)
         ctxt <- getContext
         case lookupTy n ctxt of
             Just ty -> updateContext (addCasedef n tree ty)
             Nothing -> return ()
  where
    debind (x, y) = (depat x, depat y)
    depat (Bind n (PVar t) sc) = depat (instantiate (P Bound n t) sc)
    depat x = x

elabVal :: ElabInfo -> PTerm -> Idris (Term, Type)
elabVal info tm
   = do ctxt <- getContext
        logLvl 10 (show tm)
        (tm', _) <- tclift $ elaborate ctxt (MN 0 "val") infP
                               (build True (infTerm tm))
        logLvl 3 ("Value: " ++ show tm')
        let vtm = getInferTerm tm'
        iLOG (show vtm)
        tclift $ recheck ctxt [] vtm

elabClause :: ElabInfo -> PClause -> Idris (Term, Term)
elabClause info (PClause _ lhs rhs whereblock) 
   = do ctxt <- getContext
        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        (lhs', _) <- tclift $ elaborate ctxt (MN 0 "patLHS") infP
                                (build True (infTerm lhs))
        let lhs_tm = getInferTerm lhs'
        let lhs_ty = getInferType lhs'
        logLvl 3 (show lhs_tm)
        (clhs, clhsty) <- tclift $ recheck ctxt [] lhs_tm
        -- TODO: elaborate where block here.
        -- probably the way to check the where clauses is to recursively
        -- call the elaborator with a list of variables assumed by the
        -- where block (i.e. add those variables to all types and clauses
        -- which are elaborated).

        -- Now build the RHS, using the type of the LHS as the goal.
        iLOG (showImp True rhs)
        (rhs', _) <- tclift $ elaborate ctxt (MN 0 "patRHS") clhsty
                                (do pbinds lhs_tm
                                    build False rhs
                                    psolve lhs_tm
                                    get_term)
        logLvl 2 $ "---> " ++ show rhs'
        (crhs, crhsty) <- tclift $ recheck ctxt [] rhs'
        return (clhs, crhs)
  where
    pbinds (Bind n (PVar t) sc) = do attack; patbind n 
                                     pbinds sc
    pbinds tm = return ()

    psolve (Bind n (PVar t) sc) = do solve; psolve sc
    psolve tm = return ()

    pvars (Bind n (PVar t) sc) = (n, t) : pvars sc
    pvars _ = []

elabDecl :: ElabInfo -> PDecl -> Idris ()
elabDecl info d = idrisCatch (elabDecl' info d) (\e -> iputStrLn (report e))

elabDecl' info (PFix _ _)      = return () -- nothing to elaborate
elabDecl' info (PTy n ty)      = do iLOG $ "Elaborating type decl " ++ show n
                                    elabType info n ty
elabDecl' info (PData d)       = do iLOG $ "Elaborating " ++ show d
                                    elabData info d
elabDecl' info d@(PClauses n ps) = do iLOG $ "Elaborating " ++ show n
                                      elabClauses info n ps

{- not finished...
parameterise :: [(Name, Type)] -> (Name -> Name) -> [PDecl] -> Idris [PDecl]
parameterise ns hide ds = do
    i <- getIState
    let pns = map (\ (n, t) -> (n, delab i t)) ns
    mapM (paramDecl (concatMap declared ds) hide pns) ds

paramDecl :: [Name] -> -- Names defined in this block
             (Name -> Name) -> -- what to call the lifted functions
             [(Name, PTerm)] -> -- parameters to add
             PDecl -> Idris PDecl
paramDecl ns newname ps (PTy n ty)
    = do let ty' = piBind ps ty
         return (PTy (newname n) (addNs ns newname (map fst ps) ty'))
paramDecl ns newname ps (PClauses n cs)
    = do cs' <- mapM pclause cs
         return (PClauses n cs')
  where
    pclause (PClause n lhs rhs []) 
       = return $ PClause n [] (addNs ns newname (map fst ps) lhs)
                               (addNs ns newname (map fst ps) rhs)
paramDecl ns newname ps (PData (PDatadecl n ty cons)) 
   = do let ty' = piBind ps ty
        cons' <- mapM con cons
        return (PData (PDatadecl n ty' cons'))
  where
    con (n, ty) = do let ty' = piBind ps ty
                     return (n, addNs ns newname (map fst ps) ty')
paramDecl ns newname ps d = return d
-}

addNs :: [Name] -> (Name -> Name) -> [Name] -> PTerm -> PTerm
addNs = undefined

-- Using the elaborator, convert a term in raw syntax to a fully
-- elaborated, typechecked term.
--
-- If building a pattern match, we convert undeclared variables from
-- holes to pattern bindings.

build :: Bool -> PTerm -> Elab Term
build pattern tm = do elab pattern tm
                      get_term

elab :: Bool -> PTerm -> Elab ()
elab pattern tm = do elab' tm
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
    elab' (PConstant c)  = do fill (RConstant c); solve
    elab' (PQuote r)     = do fill r; solve
    elab' (PRef n) | pattern
                         = try (do apply (Var n) []; solve)
                               (patvar n)
    elab' (PRef n)       = do apply (Var n) []; solve
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
    elab' (PApp (PRef f) args)
          = try (do ns <- apply (Var f) (map isph args)
                    solve
                    elabArgs ns (map getTm args))
                (do apply_elab f (map toElab args)
                    solve)
    elab' (PApp f [arg])
          = do simple_app (elab' f) (elab' (getTm arg))
               solve
    elab' Placeholder = fail $ "Can't deal with a placeholder here"
    elab' x = fail $ "Not implemented " ++ show x

    elabArgs [] _ = return ()
    elabArgs (n:ns) (Placeholder : args) = elabArgs ns args
    elabArgs (n:ns) (t : args) = do focus n; elab' t; elabArgs ns args
     



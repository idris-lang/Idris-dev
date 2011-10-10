{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.ElabDecls where

import Idris.AbsSyntax
import Idris.Error

import Core.TT
import Core.Elaborate
import Core.Evaluate
import Core.Typecheck
import Core.CaseTree

import Control.Monad

elabType :: Name -> PTerm -> Idris ()
elabType n ty 
    = do ctxt <- getContext
         (ty', log) <- tclift $ elaborate ctxt n (Set 0) (build False ty)
         (cty, _)   <- tclift $ recheck ctxt [] ty'
         logLvl 2 $ "---> " ++ show cty
         updateContext (addConstant n (normalise ctxt [] cty))

elabData :: PData -> Idris ()
elabData (PDatadecl n t dcons)
    = do ctxt <- getContext
         (t', log) <- tclift $ elaborate ctxt n (Set 0) (build False t)
         (cty, _)  <- tclift $ recheck ctxt [] t'
         logLvl 2 $ "---> " ++ show cty
         updateContext (addConstant n cty) -- temporary, to check cons
         cons <- mapM elabCon dcons
         setContext (addDatatype (Data n cty cons) ctxt)

elabCon :: (Name, PTerm) -> Idris (Name, Type)
elabCon (n, t)
    = do ctxt <- getContext
         iLOG $ "Constructor " ++ show n ++ " : " ++ showImp True t
         (t', log) <- tclift $ elaborate ctxt n (Set 0) (build False t)
--          iLOG $ "Rechecking " ++ show t'
         (cty, _)  <- tclift $ recheck ctxt [] t'
         logLvl 2 $ "---> " ++ show n ++ " : " ++ show cty
         return (n, cty)

elabClauses :: Name -> [PClause] -> Idris ()
elabClauses n cs 
    = do pats <- mapM elabClause cs
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

elabVal :: PTerm -> Idris (Term, Type)
elabVal tm
   = do ctxt <- getContext
        (tm', _) <- tclift $ elaborate ctxt (MN 0 "val") infP
                               (build True (infTerm tm))
        let vtm = getInferTerm tm'
        iLOG (show vtm)
        tclift $ recheck ctxt [] vtm

elabClause :: PClause -> Idris (Term, Term)
elabClause (PClause _ lhs rhs) 
   = do ctxt <- getContext
        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        (lhs', _) <- tclift $ elaborate ctxt (MN 0 "patLHS") infP
                                (build True (infTerm lhs))
        let lhs_tm = getInferTerm lhs'
        let lhs_ty = getInferType lhs'
        (clhs, clhsty) <- tclift $ recheck ctxt [] lhs_tm
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

elabDecl :: PDecl -> Idris ()
elabDecl d = idrisCatch (elabDecl' d) (\e -> iputStrLn (report e))

elabDecl' (PFix _ _)      = return () -- nothing to elaborate
elabDecl' (PTy n ty)      = do iLOG $ "Elaborating type decl " ++ show n
                               elabType n ty
elabDecl' (PData d)       = do iLOG $ "Elaborating " ++ show d
                               elabData d
elabDecl' d@(PClauses n ps) = do iLOG $ "Elaborating " ++ show n
                                 elabClauses n ps

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
    isph (_, Placeholder) = True
    isph _ = False

    toElab (_, Placeholder) = Nothing
    toElab (_, v) = Just (elab' v)

    mkPat = do hs <- get_holes
               case hs of
                  (h: hs) -> do patvar h; mkPat
                  [] -> return ()

    elab' PSet           = do exact (RSet 0); solve
    elab' (PQuote r)     = do exact r; solve
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
    elab' (PApp (PRef f) imps args)
          = try (do ns <- apply (Var f) (map isph imps ++ map (\x -> False) args)
                    solve
                    elabArgs ns (map snd imps ++ args))
                (do apply_elab f (map toElab imps ++ map (Just . elab') args)
                    solve)
    elab' (PApp f [] [arg])
          = do simple_app (elab' f) (elab' arg)
               solve
    elab' x = fail $ "Not implemented " ++ show x

    elabArgs [] _ = return ()
    elabArgs (n:ns) (Placeholder : args) = elabArgs ns args
    elabArgs (n:ns) (t : args) = do focus n; elab' t; elabArgs ns args
     



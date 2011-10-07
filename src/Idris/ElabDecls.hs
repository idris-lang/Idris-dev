{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor #-}

module Idris.ElabDecls where

import Idris.AbsSyntax

import Core.TT
import Core.Elaborate
import Core.Evaluate
import Core.Typecheck

elabType :: Name -> PTerm -> Idris ()
elabType n ty 
    = do ctxt <- getContext
         (ty', log) <- tclift $ elaborate ctxt n (Set 0) (build False ty)
         (cty, _)   <- tclift $ recheck ctxt [] ty'
         iLOG $ "---> " ++ show cty
         updateContext (addConstant n cty)

elabData :: PData -> Idris ()
elabData (PDatadecl n t dcons)
    = do ctxt <- getContext
         (t', log) <- tclift $ elaborate ctxt n (Set 0) (build False t)
         (cty, _)  <- tclift $ recheck ctxt [] t'
         iLOG $ "---> " ++ show cty
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
         iLOG $ "---> " ++ show n ++ " : " ++ show cty
         return (n, cty)

elabClauses :: [PClause] -> Idris ()
elabClauses _ = return ()

elabClause :: PClause -> Idris ()
elabClause _ = return ()

elabDecl :: PDecl -> Idris ()
elabDecl d = idrisCatch (elabDecl' d) (\e -> iputStrLn (show e))

elabDecl' (PFix _ _)      = return () -- nothing to elaborate
elabDecl' (PTy n ty)      = do iLOG $ "Elaborating type decl " ++ show n
                               elabType n ty
elabDecl' (PData d)       = do iLOG $ "Elaborating " ++ show d
                               elabData d
elabDecl' d@(PClauses ps) = do iLOG $ "Elaborating " ++ show d
                               elabClauses ps

-- Using the elaborator, convert a term in raw syntax to a fully
-- elaborated, typechecked term.
--
-- If building a pattern match, we convert undeclared variables from
-- holes to pattern bindings.

build :: Bool -> PTerm -> Elab Term
build pattern tm = do elab pattern tm
                      get_term 

elab :: Bool -> PTerm -> Elab ()
elab pattern tm = elab' tm
  where
    isph (_, Placeholder) = True
    isph _ = False

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
          = do ns <- apply (Var f) (map isph imps ++ map (\x -> False) args)
               solve
               elabArgs ns (map snd imps ++ args) 
    elab' x = fail $ "Not implemented " ++ show x

    elabArgs [] _ = return ()
    elabArgs (n:ns) (Placeholder : args) = elabArgs ns args
    elabArgs (n:ns) (t : args) = do focus n; elab' t; elabArgs ns args
     



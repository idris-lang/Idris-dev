{-|
Module      : Idris.PartialEval
Description : Implementation of a partial evaluator.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}

module Idris.PartialEval(
    partial_eval, getSpecApps, specType
  , mkPE_TyDecl, mkPE_TermDecl, PEArgType(..)
  , pe_app, pe_def, pe_clauses, pe_simple
  ) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate

import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Debug.Trace

-- | Data type representing binding-time annotations for partial evaluation of arguments
data PEArgType = ImplicitS Name -- ^ Implicit static argument
               | ImplicitD Name -- ^ Implicit dynamic argument
               | ConstraintS    -- ^ Implementation constraint
               | ConstraintD    -- ^ Implementation constraint
               | ExplicitS      -- ^ Explicit static argument
               | ExplicitD      -- ^ Explicit dynamic argument
               | UnifiedD       -- ^ Erasable dynamic argument (found under unification)
  deriving (Eq, Show)

-- | A partially evaluated function. pe_app captures the lhs of the
-- new definition, pe_def captures the rhs, and pe_clauses is the
-- specialised implementation.
--
-- pe_simple is set if the result is always reducible, because in such
-- a case we'll also need to reduce the static argument
data PEDecl = PEDecl { pe_app :: PTerm, -- new application
                       pe_def :: PTerm, -- old application
                       pe_clauses :: [(PTerm, PTerm)], -- clauses of new application
                       pe_simple :: Bool -- if just one reducible clause
                     }

-- | Partially evaluates given terms under the given context.
-- It is an error if partial evaluation fails to make any progress.
-- Making progress is defined as: all of the names given with explicit
-- reduction limits (in practice, the function being specialised)
-- must have reduced at least once.
-- If we don't do this, we might end up making an infinite function after
-- applying the transformation.
partial_eval :: Context
            -> [(Name, Maybe Int)]
            -> [Either Term (Term, Term)]
            -> Maybe [Either Term (Term, Term)]
partial_eval ctxt ns_in tms = mapM peClause tms where
   ns = squash ns_in
   squash ((n, Just x) : ns)
       | Just (Just y) <- lookup n ns
                   = squash ((n, Just (x + y)) : drop n ns)
       | otherwise = (n, Just x) : squash ns
   squash (n : ns) = n : squash ns
   squash [] = []

   drop n ((m, _) : ns) | n == m = ns
   drop n (x : ns) = x : drop n ns
   drop n [] = []

   -- If the term is not a clause, it is simply kept as is
   peClause (Left t) = Just $ Left t
   -- If the term is a clause, specialise the right hand side
   peClause (Right (lhs, rhs))
       = let (rhs', reductions) = specialise ctxt [] (map toLimit ns) rhs in
             do when (length tms == 1) $ checkProgress ns reductions
                return (Right (lhs, rhs'))

   -- TMP HACK until I do PE by WHNF rather than using main evaluator
   toLimit (n, Nothing) | isTCDict n ctxt = (n, 2)
   toLimit (n, Nothing) = (n, 65536) -- somewhat arbitrary reduction limit
   toLimit (n, Just l) = (n, l)

   checkProgress ns [] = return ()
   checkProgress ns ((n, r) : rs)
      | Just (Just start) <- lookup n ns
             = if start <= 1 || r < start then checkProgress ns rs else Nothing
      | otherwise = checkProgress ns rs

-- | Specialises the type of a partially evaluated TT function returning
-- a pair of the specialised type and the types of expected arguments.
specType :: [(PEArgType, Term)] -> Type -> (Type, [(PEArgType, Term)])
specType args ty = let (t, args') = runState (unifyEq args ty) [] in
                       (st (map fst args') t, map fst args')
  where
    -- Specialise static argument in type by let-binding provided value instead
    -- of expecting it as a function argument
    st ((ExplicitS, v) : xs) (Bind n (Pi _ _ t _) sc)
         = Bind n (Let t v) (st xs sc)
    st ((ImplicitS _, v) : xs) (Bind n (Pi _ _ t _) sc)
         = Bind n (Let t v) (st xs sc)
    st ((ConstraintS, v) : xs) (Bind n (Pi _ _ t _) sc)
         = Bind n (Let t v) (st xs sc)
    -- Erase argument from function type
    st ((UnifiedD, _) : xs) (Bind n (Pi _ _ t _) sc)
         = st xs sc
    -- Keep types as is
    st (_ : xs) (Bind n (Pi rig i t k) sc)
         = Bind n (Pi rig i t k) (st xs sc)
    st _ t = t

    -- Erase implicit dynamic argument if existing argument shares it value,
    -- by substituting the value of previous argument
    unifyEq (imp@(ImplicitD _, v) : xs) (Bind n (Pi rig i t k) sc)
         = do amap <- get
              case lookup imp amap of
                   Just n' ->
                        do put (amap ++ [((UnifiedD, Erased), n)])
                           sc' <- unifyEq xs (subst n (P Bound n' Erased) sc)
                           return (Bind n (Pi rig i t k) sc') -- erase later
                   _ -> do put (amap ++ [(imp, n)])
                           sc' <- unifyEq xs sc
                           return (Bind n (Pi rig i t k) sc')
    unifyEq (x : xs) (Bind n (Pi rig i t k) sc)
         = do args <- get
              put (args ++ [(x, n)])
              sc' <- unifyEq xs sc
              return (Bind n (Pi rig i t k) sc')
    unifyEq xs t = do args <- get
                      put (args ++ (zip xs (repeat (sUN "_"))))
                      return t

-- | Creates an Idris type declaration given current state and a
-- specialised TT function application type.
-- Can be used in combination with the output of 'specType'.
--
-- This should: specialise any static argument position, then generalise
-- over any function applications in the result.
mkPE_TyDecl :: IState -> [(PEArgType, Term)] -> Type -> PTerm
mkPE_TyDecl ist args ty = mkty args ty
  where
    mkty ((ExplicitD, v) : xs) (Bind n (Pi rig _ t k) sc)
       = PPi expl n NoFC (delab ist (generaliseIn t)) (mkty xs sc)
    mkty ((ConstraintD, v) : xs) (Bind n (Pi rig _ t k) sc)
         | concreteInterface ist t = mkty xs sc
         | interfaceConstraint ist t
             = PPi constraint n NoFC (delab ist (generaliseIn t)) (mkty xs sc)
    mkty ((ImplicitD _, v) : xs) (Bind n (Pi rig _ t k) sc)
         = PPi impl n NoFC (delab ist (generaliseIn t)) (mkty xs sc)

    mkty (_ : xs) t
       = mkty xs t
    mkty [] t = delab ist t

    generaliseIn tm = evalState (gen tm) 0

    gen tm | (P _ fn _, args) <- unApply tm,
             isFnName fn (tt_ctxt ist)
        = do nm <- get
             put (nm + 1)
             return (P Bound (sMN nm "spec") Erased)
    gen (App s f a) = App s <$> gen f <*> gen a
    gen tm = return tm

-- | Checks if a given argument is an interface constraint argument
interfaceConstraint :: Idris.AbsSyntax.IState -> TT Name -> Bool
interfaceConstraint ist v
    | (P _ c _, args) <- unApply v = case lookupCtxt c (idris_interfaces ist) of
                                          [_] -> True
                                          _ -> False
    | otherwise = False

-- | Checks if the given arguments of an interface constraint are all either constants
-- or references (i.e. that it doesn't contain any complex terms).
concreteInterface :: IState -> TT Name -> Bool
concreteInterface ist v
    | not (interfaceConstraint ist v) = False
    | (P _ c _, args) <- unApply v = all concrete args
    | otherwise = False
  where concrete (Constant _) = True
        concrete tm | (P _ n _, args) <- unApply tm
                         = case lookupTy n (tt_ctxt ist) of
                                 [_] -> all concrete args
                                 _ -> False
                    | otherwise = False

mkNewPats :: IState
          -> [(Term, Term)]      -- ^ definition to specialise
          -> [(PEArgType, Term)] -- ^ arguments to specialise with
          -> Name                -- ^ New name
          -> Name                -- ^ Specialised function name
          -> PTerm               -- ^ Default lhs
          -> PTerm               -- ^ Default rhs
          -> PEDecl
-- If all of the dynamic positions on the lhs are variables (rather than
-- patterns or constants) then we can just make a simple definition
-- directly applying the specialised function, since we know the
-- definition isn't going to block on any of the dynamic arguments
-- in this case
mkNewPats ist d ns newname sname lhs rhs | all dynVar (map fst d)
     = PEDecl lhs rhs [(lhs, rhs)] True
  where dynVar ap = case unApply ap of
                         (_, args) -> dynArgs ns args
        dynArgs _ [] = True -- can definitely reduce from here
        -- if Static, doesn't matter what the argument is
        dynArgs ((ImplicitS _, _) : ns) (a : as) = dynArgs ns as
        dynArgs ((ConstraintS, _) : ns) (a : as) = dynArgs ns as
        dynArgs ((ExplicitS, _) : ns) (a : as) = dynArgs ns as
        -- if Dynamic, it had better be a variable or we'll need to
        -- do some more work
        dynArgs (_ : ns) (V _     : as) = dynArgs ns as
        dynArgs (_ : ns) (P _ _ _ : as) = dynArgs ns as
        dynArgs _ _ = False -- and now we'll get stuck

mkNewPats ist d ns newname sname lhs rhs =
           PEDecl lhs rhs (map mkClause d) False
  where
    mkClause :: (Term, Term) -> (PTerm, PTerm)
    mkClause (oldlhs, oldrhs)
         = let (_, as) = unApply oldlhs
               lhsargs = mkLHSargs [] ns as
               lhs = PApp emptyFC (PRef emptyFC [] newname) lhsargs
               rhs = PApp emptyFC (PRef emptyFC [] sname)
                                  (mkRHSargs ns lhsargs) in
                     (lhs, rhs)

    mkLHSargs _ [] _ = []
    -- dynamics don't appear on the LHS if they're implicit
    mkLHSargs sub ((ExplicitD, t) : ns) (a : as)
         = pexp (delab ist (substNames sub a)) : mkLHSargs sub ns as
    mkLHSargs sub ((ImplicitD n, t) : ns) (a : as)
         = pimp n (delab ist (substNames sub a)) True : mkLHSargs sub ns as
    mkLHSargs sub ((ConstraintD, t) : ns) (a : as)
         = pconst (delab ist (substNames sub a)) : mkLHSargs sub ns as
    mkLHSargs sub ((UnifiedD, _) : ns) (a : as)
         = mkLHSargs sub ns as
    -- statics get dropped in any case
    mkLHSargs sub ((ImplicitS _, t) : ns) (a : as)
         = mkLHSargs (extend a t sub) ns as
    mkLHSargs sub ((ExplicitS, t) : ns) (a : as)
         = mkLHSargs (extend a t sub) ns as
    mkLHSargs sub ((ConstraintS, t) : ns) (a : as)
         = mkLHSargs (extend a t sub) ns as
    mkLHSargs sub _ [] = [] -- no more LHS

    extend (P _ n _) t sub = (n, t) : sub
    extend _ _ sub = sub

    --- 'as' are the LHS arguments
    mkRHSargs ((ExplicitS, t) : ns) as = pexp (delab ist t) : mkRHSargs ns as
    mkRHSargs ((ExplicitD, t) : ns) (a : as) = a : mkRHSargs ns as
    -- Keep the implicits on the RHS, in case they got matched on
    mkRHSargs ((ImplicitD n, t) : ns) (a : as) = a : mkRHSargs ns as
    mkRHSargs ((ImplicitS n, t) : ns) as -- Dropped from LHS
          = pimp n (delab ist t) True : mkRHSargs ns as
    mkRHSargs ((ConstraintD, t) : ns) (a : as) = a : mkRHSargs ns as
    mkRHSargs ((ConstraintS, t) : ns) as -- Dropped from LHS
          = pconst (delab ist t) : mkRHSargs ns as
    mkRHSargs (_ : ns) as = mkRHSargs ns as
    mkRHSargs _ _ = []

    mkSubst :: (Term, Term) -> Maybe (Name, Term)
    mkSubst (P _ n _, t) = Just (n, t)
    mkSubst _ = Nothing

-- | Creates a new declaration for a specialised function application.
-- Simple version at the moment: just create a version which is a direct
-- application of the function to be specialised.
-- More complex version to do: specialise the definition clause by clause
mkPE_TermDecl :: IState
              -> Name
              -> Name
              -> PTerm -- ^ Type of specialised function
              -> [(PEArgType, Term)]
              -> PEDecl
mkPE_TermDecl ist newname sname specty ns
      {- We need to erase the *dynamic* arguments
         where their *name* appears in the *type* of a later argument
         in specty.
         i.e. if a later dynamic argument depends on an earlier dynamic
         argument, we should infer the earlier one.
         Then we need to erase names from the LHS which no longer appear
         on the RHS.
         -}
    = let deps = getDepNames (eraseRet specty)
          lhs = eraseDeps deps $
                  PApp emptyFC (PRef emptyFC [] newname) (mkp ns)
          rhs = eraseDeps deps $
                  delab ist (mkApp (P Ref sname Erased) (map snd ns))
          patdef = -- trace (showTmImpls specty ++ "\n" ++ showTmImpls lhs ++ "\n"
                   --      ++ showTmImpls rhs) $
                   lookupCtxtExact sname (idris_patdefs ist)
          newpats = case patdef of
                         Nothing -> PEDecl lhs rhs [(lhs, rhs)] True
                         Just d -> mkNewPats ist (getPats d) ns
                                             newname sname lhs rhs in
          newpats where

  getPats (ps, _) = map (\(_, lhs, rhs) -> (lhs, rhs)) ps

  eraseRet (PPi p n fc ty sc) = PPi p n fc ty (eraseRet sc)
  eraseRet _ = Placeholder

  -- Get names used in later arguments; assume we've called eraseRet so there's
  -- no names going to appear in return type
  getDepNames (PPi _ n _ _ sc)
        | n `elem` allNamesIn sc = n : getDepNames sc
        | otherwise = getDepNames sc
  getDepNames tm = []

  mkp [] = []
  mkp ((ExplicitD, tm) : tms) = pexp (delab ist tm) : mkp tms
  mkp ((ImplicitD n, tm) : tms) = pimp n (delab ist tm) True : mkp tms
  mkp (_ : tms) = mkp tms

  eraseDeps ns tm = mapPT (deImp ns) tm

  deImp ns (PApp fc t as) = PApp fc t (map (deImpArg ns) as)
  deImp ns t = t

  deImpArg ns a | pname a `elem` ns = a { getTm = Placeholder }
                | otherwise = a

-- | Get specialised applications for a given function
getSpecApps :: IState
            -> [Name]
            -> Term
            -> [(Name, [(PEArgType, Term)])]
getSpecApps ist env tm = ga env (explicitNames tm) where

--     staticArg env True _ tm@(P _ n _) _ | n `elem` env = Just (True, tm)
--     staticArg env True _ tm@(App f a) _ | (P _ n _, args) <- unApply tm,
--                                            n `elem` env = Just (True, tm)
    staticArg env True imp tm n
         | Just n <- imparg imp = (ImplicitS n, tm)
         | constrarg imp = (ConstraintS, tm)
         | otherwise = (ExplicitS, tm)

    staticArg env False imp tm n
         | Just nm <- imparg imp = (ImplicitD nm, (P Ref (sUN (show n ++ "arg")) Erased))
         | constrarg imp = (ConstraintD, tm)
         | otherwise = (ExplicitD, (P Ref (sUN (show n ++ "arg")) Erased))

    imparg (PExp _ _ _ _) = Nothing
    imparg (PConstraint _ _ _ _) = Nothing
    imparg arg = Just (pname arg)

    constrarg (PConstraint _ _ _ _) = True
    constrarg arg = False

    buildApp env [] [] _ _ = []
    buildApp env (s:ss) (i:is) (a:as) (n:ns)
        = let s' = staticArg env s i a n
              ss' = buildApp env ss is as ns in
              (s' : ss')

    -- if we have a *defined* function that has static arguments,
    -- it will become a specialised application
    ga env tm@(App _ f a) | (P _ n _, args) <- unApply tm,
                          n `notElem` map fst (idris_metavars ist) =
        ga env f ++ ga env a ++
          case (lookupCtxtExact n (idris_statics ist),
                  lookupCtxtExact n (idris_implicits ist)) of
               (Just statics, Just imps) ->
                   if (length statics == length args && or statics
                          && specialisable (tt_ctxt ist) n) then
                      case buildApp env statics imps args [0..] of
                           args -> [(n, args)]
--                            _ -> []
                      else []
               _ -> []
    ga env (Bind n (Let t v) sc) = ga env v ++ ga (n : env) sc
    ga env (Bind n t sc) = ga (n : env) sc
    ga env t = []

    -- A function is only specialisable if there are no overlapping
    -- cases in the case tree (otherwise the partial evaluation could
    -- easily get stuck)
    specialisable :: Context -> Name -> Bool
    specialisable ctxt n = case lookupDefExact n ctxt of
                                Just (CaseOp _ _ _ _ _ cds) ->
                                     noOverlap (snd (cases_compiletime cds))
                                _ -> False

    noOverlap :: SC -> Bool
    noOverlap (Case _ _ [DefaultCase sc]) = noOverlap sc
    noOverlap (Case _ _ alts) = noOverlapAlts alts
    noOverlap _ = True

    -- There's an overlap if the case tree has a default case along with
    -- some other cases. It's fine if there's a default case on its own.
    noOverlapAlts (ConCase _ _ _ sc : rest)
        = noOverlapAlts rest && noOverlap sc
    noOverlapAlts (FnCase _ _ sc : rest) = noOverlapAlts rest
    noOverlapAlts (ConstCase _ sc : rest)
        = noOverlapAlts rest && noOverlap sc
    noOverlapAlts (SucCase _ sc : rest)
        = noOverlapAlts rest && noOverlap sc
    noOverlapAlts (DefaultCase _ : _) = False
    noOverlapAlts _ = True

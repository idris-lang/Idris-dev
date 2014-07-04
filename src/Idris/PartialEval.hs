{-# LANGUAGE PatternGuards #-}

module Idris.PartialEval(partial_eval, getSpecApps, specType,
                         mkPE_TyDecl, mkPE_TermDecl, PEArgType(..)) where

import Idris.AbsSyntax
import Idris.Delaborate

import Idris.Core.TT
import Idris.Core.Evaluate

import Control.Monad.State
import Debug.Trace

-- | Partially evaluates given terms under the given context.
partial_eval :: Context -> [(Name, Maybe Int)] ->
                [Either Term (Term, Term)] ->
                [Either Term (Term, Term)]
partial_eval ctxt ns tms = map peClause tms where
   -- If the term is not a clause, it is simply kept as is
   peClause (Left t) = Left t
   -- If the term is a clause, specialise the right hand side
   peClause (Right (lhs, rhs))
       = let rhs' = specialise ctxt [] (map toLimit ns) rhs in
             Right (lhs, rhs')

   toLimit (n, Nothing) = (n, 65536) -- somewhat arbitrary reduction limit
   toLimit (n, Just l) = (n, l)

-- | Specialises the type of a partially evaluated TT function returning
-- a pair of the specialised type and the types of expected arguments.
specType :: [(PEArgType, Term)] -> Type -> (Type, [(PEArgType, Term)])
specType args ty = let (t, args') = runState (unifyEq args ty) [] in
                       (st (map fst args') t, map fst args')
  where
    -- Specialise static argument in type by let-binding provided value instead
    -- of expecting it as a function argument
    st ((ExplicitS, v) : xs) (Bind n (Pi t) sc)
         = Bind n (Let t v) (st xs sc)
    st ((ImplicitS, v) : xs) (Bind n (Pi t) sc)
         = Bind n (Let t v) (st xs sc)
    -- Erase argument from function type
    st ((UnifiedD, _) : xs) (Bind n (Pi t) sc)
         = st xs sc
    -- Keep types as is
    st (_ : xs) (Bind n (Pi t) sc)
         = Bind n (Pi t) (st xs sc)
    st _ t = t

    -- Erase implicit dynamic argument if existing argument shares it value,
    -- by substituting the value of previous argument
    unifyEq (imp@(ImplicitD, v) : xs) (Bind n (Pi t) sc)
         = do amap <- get
              case lookup imp amap of
                   Just n' -> 
                        do put (amap ++ [((UnifiedD, Erased), n)])
                           sc' <- unifyEq xs (subst n (P Bound n' Erased) sc)
                           return (Bind n (Pi t) sc') -- erase later
                   _ -> do put (amap ++ [(imp, n)])
                           sc' <- unifyEq xs sc
                           return (Bind n (Pi t) sc')
    unifyEq (x : xs) (Bind n (Pi t) sc)
         = do args <- get
              put (args ++ [(x, n)])
              sc' <- unifyEq xs sc
              return (Bind n (Pi t) sc')
    unifyEq xs t = do args <- get
                      put (args ++ (zip xs (repeat (sUN "_"))))
                      return t

-- | Creates an Idris type declaration given current state and a specialised TT function application type.
-- Can be used in combination with the output of 'specType'.
mkPE_TyDecl :: IState -> [(PEArgType, Term)] -> Type -> PTerm
mkPE_TyDecl ist args ty = mkty args ty
  where
    mkty ((ExplicitD, v) : xs) (Bind n (Pi t) sc)
       = PPi expl n (delab ist t) (mkty xs sc)
    mkty ((ImplicitD, v) : xs) (Bind n (Pi t) sc)
         | concreteClass ist t = mkty xs sc
         | classConstraint ist t 
             = PPi constraint n (delab ist t) (mkty xs sc)
         | otherwise = PPi impl n (delab ist t) (mkty xs sc)
    mkty (_ : xs) t
       = mkty xs t
    mkty [] t = delab ist t

-- | Checks if a given argument is a type class constraint argument
classConstraint ist v
    | (P _ c _, args) <- unApply v = case lookupCtxt c (idris_classes ist) of
                                          [_] -> True
                                          _ -> False
    | otherwise = False

-- | Checks if the given arguments of a type class constraint are all either constants
-- or references (i.e. that it doesn't contain any complex terms).
concreteClass ist v
    | not (classConstraint ist v) = False
    | (P _ c _, args) <- unApply v = all concrete args
    | otherwise = False
  where concrete (Constant _) = True
        concrete tm | (P _ n _, args) <- unApply tm 
                         = case lookupTy n (tt_ctxt ist) of
                                 [_] -> all concrete args
                                 _ -> False
                    | otherwise = False

-- | Creates a new clause for a specialised function application
mkPE_TermDecl :: IState -> Name -> Name ->
                 [(PEArgType, Term)] -> [(PTerm, PTerm)]
mkPE_TermDecl ist newname sname ns 
    = let lhs = PApp emptyFC (PRef emptyFC newname) (map pexp (mkp ns)) 
          rhs = eraseImps $ delab ist (mkApp (P Ref sname Erased) (map snd ns)) in 
          [(lhs, rhs)] where
  mkp [] = []
  mkp ((ExplicitD, tm) : tms) = delab ist tm : mkp tms
  mkp (_ : tms) = mkp tms

  eraseImps tm = mapPT deImp tm

  deImp (PApp fc t as) = PApp fc t (map deImpArg as)
  deImp t = t

  deImpArg a@(PImp _ _ _ _ _) = a { getTm = Placeholder }
  deImpArg a = a

-- | Data type representing binding-time annotations for partial evaluation of arguments
data PEArgType = ImplicitS -- ^ Implicit static argument
               | ImplicitD -- ^ Implicit dynamic argument
               | ExplicitS -- ^ Explicit static argument
               | ExplicitD -- ^ Explicit dynamic argument
               | UnifiedD  -- ^ Erasable dynamic argument (found under unification)
  deriving (Eq, Show)

-- | Get specialised applications for a given function
getSpecApps :: IState -> [Name] -> Term -> 
               [(Name, [(PEArgType, Term)])]
getSpecApps ist env tm = ga env (explicitNames tm) where

--     staticArg env True _ tm@(P _ n _) _ | n `elem` env = Just (True, tm)
--     staticArg env True _ tm@(App f a) _ | (P _ n _, args) <- unApply tm,
--                                            n `elem` env = Just (True, tm)
    staticArg env x imp tm n
         | x && imparg imp = (ImplicitS, tm)
         | x = (ExplicitS, tm)
         | imparg imp = (ImplicitD, tm)
         | otherwise = (ExplicitD, (P Ref (sUN (show n ++ "arg")) Erased))

    imparg (PExp _ _ _ _) = False
    imparg _ = True

    buildApp env [] [] _ _ = []
    buildApp env (s:ss) (i:is) (a:as) (n:ns)
        = let s' = staticArg env s i a n
              ss' = buildApp env ss is as ns in
              (s' : ss')
 
    ga env tm@(App f a) | (P _ n _, args) <- unApply tm =
      ga env f ++ ga env a ++
        case (lookupCtxt n (idris_statics ist),
                lookupCtxt n (idris_implicits ist)) of
             ([statics], [imps]) -> 
                 if (length statics == length args && or statics) then
                    case buildApp env statics imps args [0..] of
                         args -> [(n, args)]
--                          _ -> []
                    else []
             _ -> []
    ga env (Bind n t sc) = ga (n : env) sc
    ga env t = []



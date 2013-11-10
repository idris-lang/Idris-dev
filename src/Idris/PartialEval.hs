{-# LANGUAGE PatternGuards #-}

module Idris.PartialEval(partial_eval, getSpecApps, specType,
                         mkPE_TyDecl, mkPE_TermDecl, PEArgType(..)) where

import Idris.AbsSyntax
import Idris.Delaborate

import Core.TT
import Core.Evaluate

import Debug.Trace

partial_eval :: Context -> [(Name, Maybe Int)] ->
                [Either Term (Term, Term)] ->
                [Either Term (Term, Term)]
partial_eval ctxt ns tms = map peClause tms where
   peClause (Left t) = Left t
   peClause (Right (lhs, rhs))
       = let rhs' = specialise ctxt [] (map toLimit ns) rhs in
             Right (lhs, rhs')

   toLimit (n, Nothing) = (n, 65536) -- somewhat arbitrary reduction limit
   toLimit (n, Just l) = (n, l)

specType :: [(PEArgType, Term)] -> Type -> Type
specType ((ExplicitS, v) : xs) (Bind n (Pi t) sc)
         = Bind n (Let t v) (specType xs sc)
specType ((ImplicitS, v) : xs) (Bind n (Pi t) sc)
         = Bind n (Let t v) (specType xs sc)
specType (_ : xs) (Bind n (Pi t) sc)
         = Bind n (Pi t) (specType xs sc)
specType _ t = t

mkPE_TyDecl :: IState -> [(PEArgType, Term)] -> Type -> PTerm
mkPE_TyDecl ist ((ExplicitD, v) : xs) (Bind n (Pi t) sc)
   = PPi expl n (delab ist t) (mkPE_TyDecl ist xs sc)
mkPE_TyDecl ist ((ImplicitD, v) : xs) (Bind n (Pi t) sc)
     | concreteClass ist t = mkPE_TyDecl ist xs sc
     | classConstraint ist t 
         = PPi constraint n (delab ist t) (mkPE_TyDecl ist xs sc)
     | otherwise = PPi impl n (delab ist t) (mkPE_TyDecl ist xs sc)
mkPE_TyDecl ist (_ : xs) t
   = mkPE_TyDecl ist xs t
mkPE_TyDecl ist [] t = delab ist t

classConstraint ist v
    | (P _ c _, args) <- unApply v = case lookupCtxt c (idris_classes ist) of
                                          [_] -> True
                                          _ -> False
    | otherwise = False

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

  deImpArg a@(PImp _ _ _ _ _ _) = a { getTm = Placeholder }
  deImpArg a = a

data PEArgType = ImplicitS | ImplicitD
               | ExplicitS | ExplicitD
  deriving Show

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
         | otherwise = (ExplicitD, (P Ref (MN n "arg") Erased))

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



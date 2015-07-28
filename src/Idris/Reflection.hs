{-| Code related to Idris's reflection system. This module contains
quoters and unquoters along with some supporting datatypes.
-}
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -fwarn-unused-imports #-}
module Idris.Reflection where

import Control.Applicative ((<$>), (<*>), pure)
import Control.Monad (liftM, liftM2, liftM3)
import Data.Maybe (catMaybes)
import Data.List ((\\))
import qualified Data.Text as T

import Idris.Core.Elaborate (claim, fill, focus, getNameFrom, initElaborator,
                             movelast, runElab, solve)
import Idris.Core.Evaluate (Def(TyDecl), initContext, lookupDefExact, lookupTyExact)
import Idris.Core.TT

import Idris.AbsSyntaxTree (ArgOpt(..),ElabD, IState(tt_ctxt, idris_implicits,idris_datatypes),
                            PArg'(..), PArg, PTactic, PTactic'(..), PTerm(..),
                            initEState, pairCon, pairTy)
import Idris.Delaborate (delab)

data RErasure = RErased | RNotErased deriving Show

data RArg = RExplicit   { argName :: Name, argErased :: RErasure, argTy :: Raw }
          | RImplicit   { argName :: Name, argErased :: RErasure, argTy :: Raw }
          | RConstraint { argName :: Name, argErased :: RErasure, argTy :: Raw }
  deriving Show

data RTyDecl = RDeclare Name [RArg] Raw deriving Show

data RTyConArg = RParameter { tcArgName :: Name, tcArgErased :: RErasure, tcArgTy :: Raw }
               | RIndex     { tcArgName :: Name, tcArgErased :: RErasure, tcArgTy :: Raw }
  deriving Show

data RDatatype = RDatatype Name [RTyConArg] Raw [(Name, [RArg], Raw)] deriving Show

rArgOpts :: RErasure -> [ArgOpt]
rArgOpts RErased = [InaccessibleArg]
rArgOpts _ = []

rArgToPArg :: RArg -> PArg
rArgToPArg (RExplicit n e _) = PExp 0 (rArgOpts e) n Placeholder
rArgToPArg (RImplicit n e _) = PImp 0 False (rArgOpts e) n Placeholder
rArgToPArg (RConstraint n e _) = PConstraint 0 (rArgOpts e) n Placeholder

data RFunClause = RMkFunClause Raw Raw
                | RMkImpossibleClause Raw
                deriving Show

data RFunDefn = RDefineFun Name [RFunClause] deriving Show

-- | Prefix a name with the "Language.Reflection" namespace
reflm :: String -> Name
reflm n = sNS (sUN n) ["Reflection", "Language"]

-- | Prefix a name with the "Language.Reflection.Elab" namespace
tacN :: String -> Name
tacN str = sNS (sUN str) ["Elab", "Reflection", "Language"]

-- | Reify tactics from their reflected representation
reify :: IState -> Term -> ElabD PTactic
reify _ (P _ n _) | n == reflm "Intros" = return Intros
reify _ (P _ n _) | n == reflm "Trivial" = return Trivial
reify _ (P _ n _) | n == reflm "Instance" = return TCInstance
reify _ (P _ n _) | n == reflm "Solve" = return Solve
reify _ (P _ n _) | n == reflm "Compute" = return Compute
reify _ (P _ n _) | n == reflm "Skip" = return Skip
reify _ (P _ n _) | n == reflm "SourceFC" = return SourceFC
reify _ (P _ n _) | n == reflm "Unfocus" = return Unfocus
reify ist t@(App _ _ _)
          | (P _ f _, args) <- unApply t = reifyApp ist f args
reify _ t = fail ("Unknown tactic " ++ show t)

reifyApp :: IState -> Name -> [Term] -> ElabD PTactic
reifyApp ist t [l, r] | t == reflm "Try" = liftM2 Try (reify ist l) (reify ist r)
reifyApp _ t [Constant (I i)]
           | t == reflm "Search" = return (ProofSearch True True i Nothing [])
reifyApp _ t [x]
           | t == reflm "Refine" = do n <- reifyTTName x
                                      return $ Refine n []
reifyApp ist t [n, ty] | t == reflm "Claim" = do n' <- reifyTTName n
                                                 goal <- reifyTT ty
                                                 return $ Claim n' (delab ist goal)
reifyApp ist t [l, r] | t == reflm "Seq" = liftM2 TSeq (reify ist l) (reify ist r)
reifyApp ist t [Constant (Str n), x]
             | t == reflm "GoalType" = liftM (GoalType n) (reify ist x)
reifyApp _ t [n] | t == reflm "Intro" = liftM (Intro . (:[])) (reifyTTName n)
reifyApp ist t [t'] | t == reflm "Induction" = liftM (Induction . delab ist) (reifyTT t')
reifyApp ist t [t'] | t == reflm "Case" = liftM (CaseTac . delab ist) (reifyTT t')
reifyApp ist t [t']
             | t == reflm "ApplyTactic" = liftM (ApplyTactic . delab ist) (reifyTT t')
reifyApp ist t [t']
             | t == reflm "Reflect" = liftM (Reflect . delab ist) (reifyTT t')
reifyApp ist t [t']
             | t == reflm "ByReflection" = liftM (ByReflection . delab ist) (reifyTT t')
reifyApp _ t [t']
           | t == reflm "Fill" = liftM (Fill . PQuote) (reifyRaw t')
reifyApp ist t [t']
             | t == reflm "Exact" = liftM (Exact . delab ist) (reifyTT t')
reifyApp ist t [x]
             | t == reflm "Focus" = liftM Focus (reifyTTName x)
reifyApp ist t [t']
             | t == reflm "Rewrite" = liftM (Rewrite . delab ist) (reifyTT t')
reifyApp ist t [n, t']
             | t == reflm "LetTac" = do n'  <- reifyTTName n
                                        t'' <- reifyTT t'
                                        return $ LetTac n' (delab ist t')
reifyApp ist t [n, tt', t']
             | t == reflm "LetTacTy" = do n'   <- reifyTTName n
                                          tt'' <- reifyTT tt'
                                          t''  <- reifyTT t'
                                          return $ LetTacTy n' (delab ist tt'') (delab ist t'')
reifyApp ist t [errs]
             | t == reflm "Fail" = fmap TFail (reifyReportParts errs)
reifyApp _ f args = fail ("Unknown tactic " ++ show (f, args)) -- shouldn't happen

reifyBool :: Term -> ElabD Bool
reifyBool (P _ n _) | n == sNS (sUN "True") ["Bool", "Prelude"] = return True
                    | n == sNS (sUN "False") ["Bool", "Prelude"] = return False
reifyBool tm = fail $ "Not a Boolean: " ++ show tm

reifyInt :: Term -> ElabD Int
reifyInt (Constant (I i)) = return i
reifyInt tm = fail $ "Not an Int: " ++ show tm

reifyPair :: (Term -> ElabD a) -> (Term -> ElabD b) -> Term -> ElabD (a, b)
reifyPair left right (App _ (App _ (App _ (App _ (P _ n _) _) _) x) y)
  | n == pairCon = liftM2 (,) (left x) (right y)
reifyPair left right tm = fail $ "Not a pair: " ++ show tm

reifyList :: (Term -> ElabD a) -> Term -> ElabD [a]
reifyList getElt lst =
  case unList lst of
    Nothing -> fail "Couldn't reify a list"
    Just xs -> mapM getElt xs

reifyReportParts :: Term -> ElabD [ErrorReportPart]
reifyReportParts errs =
  case unList errs of
    Nothing -> fail "Failed to reify errors"
    Just errs' ->
      let parts = mapM reifyReportPart errs' in
      case parts of
        Left err -> fail $ "Couldn't reify \"Fail\" tactic - " ++ show err
        Right errs'' ->
          return errs''

-- | Reify terms from their reflected representation
reifyTT :: Term -> ElabD Term
reifyTT t@(App _ _ _)
        | (P _ f _, args) <- unApply t = reifyTTApp f args
reifyTT t@(P _ n _)
        | n == reflm "Erased" = return $ Erased
reifyTT t@(P _ n _)
        | n == reflm "Impossible" = return $ Impossible
reifyTT t = fail ("Unknown reflection term: " ++ show t)

reifyTTApp :: Name -> [Term] -> ElabD Term
reifyTTApp t [nt, n, x]
           | t == reflm "P" = do nt' <- reifyTTNameType nt
                                 n'  <- reifyTTName n
                                 x'  <- reifyTT x
                                 return $ P nt' n' x'
reifyTTApp t [Constant (I i)]
           | t == reflm "V" = return $ V i
reifyTTApp t [n, b, x]
           | t == reflm "Bind" = do n' <- reifyTTName n
                                    b' <- reifyTTBinder reifyTT (reflm "TT") b
                                    x' <- reifyTT x
                                    return $ Bind n' b' x'
reifyTTApp t [f, x]
           | t == reflm "App" = do f' <- reifyTT f
                                   x' <- reifyTT x
                                   return $ App Complete f' x'
reifyTTApp t [c]
           | t == reflm "TConst" = liftM Constant (reifyTTConst c)
reifyTTApp t [t', Constant (I i)]
           | t == reflm "Proj" = do t'' <- reifyTT t'
                                    return $ Proj t'' i
reifyTTApp t [tt]
           | t == reflm "TType" = liftM TType (reifyTTUExp tt)
reifyTTApp t [tt]
           | t == reflm "UType" = liftM UType (reifyUniverse tt)
reifyTTApp t args = fail ("Unknown reflection term: " ++ show (t, args))

reifyUniverse :: Term -> ElabD Universe
reifyUniverse (P _ n _) | n == reflm "AllTypes" = return AllTypes
                        | n == reflm "UniqueType" = return UniqueType
                        | n == reflm "NullType" = return NullType
reifyUniverse tm = fail ("Unknown reflection universe: " ++ show tm)

-- | Reify raw terms from their reflected representation
reifyRaw :: Term -> ElabD Raw
reifyRaw t@(App _ _ _)
         | (P _ f _, args) <- unApply t = reifyRawApp f args
reifyRaw t@(P _ n _)
         | n == reflm "RType" = return $ RType
reifyRaw t = fail ("Unknown reflection raw term in reifyRaw: " ++ show t)

reifyRawApp :: Name -> [Term] -> ElabD Raw
reifyRawApp t [n]
            | t == reflm "Var" = liftM Var (reifyTTName n)
reifyRawApp t [n, b, x]
            | t == reflm "RBind" = do n' <- reifyTTName n
                                      b' <- reifyTTBinder reifyRaw (reflm "Raw") b
                                      x' <- reifyRaw x
                                      return $ RBind n' b' x'
reifyRawApp t [f, x]
            | t == reflm "RApp" = liftM2 RApp (reifyRaw f) (reifyRaw x)
reifyRawApp t [t']
            | t == reflm "RForce" = liftM RForce (reifyRaw t')
reifyRawApp t [c]
            | t == reflm "RConstant" = liftM RConstant (reifyTTConst c)
reifyRawApp t args = fail ("Unknown reflection raw term in reifyRawApp: " ++ show (t, args))

reifyTTName :: Term -> ElabD Name
reifyTTName t
            | (P _ f _, args) <- unApply t = reifyTTNameApp f args
reifyTTName t = fail ("Unknown reflection term name: " ++ show t)

reifyTTNameApp :: Name -> [Term] -> ElabD Name
reifyTTNameApp t [Constant (Str n)]
               | t == reflm "UN" = return $ sUN n
reifyTTNameApp t [n, ns]
               | t == reflm "NS" = do n'  <- reifyTTName n
                                      ns' <- reifyTTNamespace ns
                                      return $ sNS n' ns'
reifyTTNameApp t [Constant (I i), Constant (Str n)]
               | t == reflm "MN" = return $ sMN i n
reifyTTNameApp t [sn]
               | t == reflm "SN"
               , (P _ f _, args) <- unApply sn = SN <$> reifySN f args
  where reifySN :: Name -> [Term] -> ElabD SpecialName
        reifySN t [Constant (I i), n1, n2]
                | t == reflm "WhereN" = WhereN i <$> reifyTTName n1 <*> reifyTTName n2
        reifySN t [Constant (I i), n]
                | t == reflm "WithN" = WithN i <$> reifyTTName n
        reifySN t [n, ss]
                | t == reflm "InstanceN" =
                  case unList ss of
                    Nothing -> fail "Can't reify InstanceN strings"
                    Just ss' -> InstanceN <$> reifyTTName n <*>
                                 pure [T.pack s | Constant (Str s) <- ss']
        reifySN t [n, Constant (Str s)]
                | t == reflm "ParentN" =
                  ParentN <$> reifyTTName n <*> pure (T.pack s)
        reifySN t [n]
                | t == reflm "MethodN" =
                  MethodN <$> reifyTTName n
        reifySN t [n]
                | t == reflm "CaseN" =
                  CaseN <$> reifyTTName n
        reifySN t [n]
                | t == reflm "ElimN" =
                  ElimN <$> reifyTTName n
        reifySN t [n]
                | t == reflm "InstanceCtorN" =
                  InstanceCtorN <$> reifyTTName n
        reifySN t [n1, n2]
                | t == reflm "MetaN" =
                  MetaN <$> reifyTTName n1 <*> reifyTTName n2
        reifySN t args = fail $ "Can't reify special name " ++ show t ++ show args
reifyTTNameApp t []
               | t == reflm "NErased" = return NErased
reifyTTNameApp t args = fail ("Unknown reflection term name: " ++ show (t, args))

reifyTTNamespace :: Term -> ElabD [String]
reifyTTNamespace t@(App _ _ _)
  = case unApply t of
      (P _ f _, [Constant StrType])
           | f == sNS (sUN "Nil") ["List", "Prelude"] -> return []
      (P _ f _, [Constant StrType, Constant (Str n), ns])
           | f == sNS (sUN "::")  ["List", "Prelude"] -> liftM (n:) (reifyTTNamespace ns)
      _ -> fail ("Unknown reflection namespace arg: " ++ show t)
reifyTTNamespace t = fail ("Unknown reflection namespace arg: " ++ show t)

reifyTTNameType :: Term -> ElabD NameType
reifyTTNameType t@(P _ n _) | n == reflm "Bound" = return $ Bound
reifyTTNameType t@(P _ n _) | n == reflm "Ref" = return $ Ref
reifyTTNameType t@(App _ _ _)
  = case unApply t of
      (P _ f _, [Constant (I tag), Constant (I num)])
           | f == reflm "DCon" -> return $ DCon tag num False -- FIXME: Uniqueness!
           | f == reflm "TCon" -> return $ TCon tag num
      _ -> fail ("Unknown reflection name type: " ++ show t)
reifyTTNameType t = fail ("Unknown reflection name type: " ++ show t)

reifyTTBinder :: (Term -> ElabD a) -> Name -> Term -> ElabD (Binder a)
reifyTTBinder reificator binderType t@(App _ _ _)
  = case unApply t of
     (P _ f _, bt:args) | forget bt == Var binderType
       -> reifyTTBinderApp reificator f args
     _ -> fail ("Mismatching binder reflection: " ++ show t)
reifyTTBinder _ _ t = fail ("Unknown reflection binder: " ++ show t)

reifyTTBinderApp :: (Term -> ElabD a) -> Name -> [Term] -> ElabD (Binder a)
reifyTTBinderApp reif f [t]
                      | f == reflm "Lam" = liftM Lam (reif t)
reifyTTBinderApp reif f [t, k]
                      | f == reflm "Pi" = liftM2 (Pi Nothing) (reif t) (reif k)
reifyTTBinderApp reif f [x, y]
                      | f == reflm "Let" = liftM2 Let (reif x) (reif y)
reifyTTBinderApp reif f [x, y]
                      | f == reflm "NLet" = liftM2 NLet (reif x) (reif y)
reifyTTBinderApp reif f [t]
                      | f == reflm "Hole" = liftM Hole (reif t)
reifyTTBinderApp reif f [t]
                      | f == reflm "GHole" = liftM (GHole 0) (reif t)
reifyTTBinderApp reif f [x, y]
                      | f == reflm "Guess" = liftM2 Guess (reif x) (reif y)
reifyTTBinderApp reif f [t]
                      | f == reflm "PVar" = liftM PVar (reif t)
reifyTTBinderApp reif f [t]
                      | f == reflm "PVTy" = liftM PVTy (reif t)
reifyTTBinderApp _ f args = fail ("Unknown reflection binder: " ++ show (f, args))

reifyTTConst :: Term -> ElabD Const
reifyTTConst (P _ n _) | n == reflm "StrType"  = return $ StrType
reifyTTConst (P _ n _) | n == reflm "VoidType" = return $ VoidType
reifyTTConst (P _ n _) | n == reflm "Forgot"   = return $ Forgot
reifyTTConst t@(App _ _ _)
             | (P _ f _, [arg]) <- unApply t   = reifyTTConstApp f arg
reifyTTConst t = fail ("Unknown reflection constant: " ++ show t)

reifyTTConstApp :: Name -> Term -> ElabD Const
reifyTTConstApp f aty
                | f == reflm "AType" = fmap AType (reifyArithTy aty)
reifyTTConstApp f (Constant c@(I _))
                | f == reflm "I"   = return $ c
reifyTTConstApp f (Constant c@(BI _))
                | f == reflm "BI"  = return $ c
reifyTTConstApp f (Constant c@(Fl _))
                | f == reflm "Fl"  = return $ c
reifyTTConstApp f (Constant c@(Ch _))
                | f == reflm "Ch"  = return $ c
reifyTTConstApp f (Constant c@(Str _))
                | f == reflm "Str" = return $ c
reifyTTConstApp f (Constant c@(B8 _))
                | f == reflm "B8"  = return $ c
reifyTTConstApp f (Constant c@(B16 _))
                | f == reflm "B16" = return $ c
reifyTTConstApp f (Constant c@(B32 _))
                | f == reflm "B32" = return $ c
reifyTTConstApp f (Constant c@(B64 _))
                | f == reflm "B64" = return $ c
reifyTTConstApp f arg = fail ("Unknown reflection constant: " ++ show (f, arg))

reifyArithTy :: Term -> ElabD ArithTy
reifyArithTy (App _ (P _ n _) intTy) | n == reflm "ATInt"   = fmap ATInt (reifyIntTy intTy)
reifyArithTy (P _ n _)             | n == reflm "ATFloat" = return ATFloat
reifyArithTy x = fail ("Couldn't reify reflected ArithTy: " ++ show x)

reifyNativeTy :: Term -> ElabD NativeTy
reifyNativeTy (P _ n _) | n == reflm "IT8" = return IT8
reifyNativeTy (P _ n _) | n == reflm "IT8" = return IT8
reifyNativeTy (P _ n _) | n == reflm "IT8" = return IT8
reifyNativeTy (P _ n _) | n == reflm "IT8" = return IT8
reifyNativeTy x = fail $ "Couldn't reify reflected NativeTy " ++ show x

reifyIntTy :: Term -> ElabD IntTy
reifyIntTy (App _ (P _ n _) nt) | n == reflm "ITFixed" = fmap ITFixed (reifyNativeTy nt)
reifyIntTy (P _ n _) | n == reflm "ITNative" = return ITNative
reifyIntTy (P _ n _) | n == reflm "ITBig" = return ITBig
reifyIntTy (P _ n _) | n == reflm "ITChar" = return ITChar
reifyIntTy tm = fail $ "The term " ++ show tm ++ " is not a reflected IntTy"

reifyTTUExp :: Term -> ElabD UExp
reifyTTUExp t@(App _ _ _)
  = case unApply t of
      (P _ f _, [Constant (I i)]) | f == reflm "UVar" -> return $ UVar i
      (P _ f _, [Constant (I i)]) | f == reflm "UVal" -> return $ UVal i
      _ -> fail ("Unknown reflection type universe expression: " ++ show t)
reifyTTUExp t = fail ("Unknown reflection type universe expression: " ++ show t)

-- | Create a reflected call to a named function/constructor
reflCall :: String -> [Raw] -> Raw
reflCall funName args
  = raw_apply (Var (reflm funName)) args

-- | Lift a term into its Language.Reflection.TT representation
reflect :: Term -> Raw
reflect = reflectTTQuote []

-- | Lift a term into its Language.Reflection.Raw representation
reflectRaw :: Raw -> Raw
reflectRaw = reflectRawQuote []

claimTy :: Name -> Raw -> ElabD Name
claimTy n ty = do n' <- getNameFrom n
                  claim n' ty
                  return n'

-- | Convert a reflected term to a more suitable form for pattern-matching.
-- In particular, the less-interesting bits are elaborated to _ patterns. This
-- happens to NameTypes, universe levels, names that are bound but not used,
-- and the type annotation field of the P constructor.
reflectTTQuotePattern :: [Name] -> Term -> ElabD ()
reflectTTQuotePattern unq (P _ n _)
  | n `elem` unq = -- the unquoted names have been claimed as TT already - just use them
    do fill (Var n) ; solve
  | otherwise =
    do tyannot <- claimTy (sMN 0 "pTyAnnot") (Var (reflm "TT"))
       movelast tyannot  -- use a _ pattern here
       nt <- getNameFrom (sMN 0 "nt")
       claim nt (Var (reflm "NameType"))
       movelast nt       -- use a _ pattern here
       n' <- getNameFrom (sMN 0 "n")
       claim n' (Var (reflm "TTName"))
       fill $ reflCall "P" [Var nt, Var n', Var tyannot]
       solve
       focus n'; reflectNameQuotePattern n
reflectTTQuotePattern unq (V n)
  = do fill $ reflCall "V" [RConstant (I n)]
       solve
reflectTTQuotePattern unq (Bind n b x)
  = do x' <- claimTy (sMN 0 "sc") (Var (reflm "TT"))
       movelast x'
       b' <- getNameFrom (sMN 0 "binder")
       claim b' (RApp (Var (sNS (sUN "Binder") ["Reflection", "Language"]))
                      (Var (sNS (sUN "TT") ["Reflection", "Language"])))
       if n `elem` freeNames x
         then do fill $ reflCall "Bind"
                                 [reflectName n,
                                  Var b',
                                  Var x']
                 solve
         else do any <- getNameFrom (sMN 0 "anyName")
                 claim any (Var (reflm "TTName"))
                 movelast any
                 fill $ reflCall "Bind"
                                 [Var any,
                                  Var b',
                                  Var x']
                 solve
       focus x'; reflectTTQuotePattern unq x
       focus b'; reflectBinderQuotePattern reflectTTQuotePattern (Var $ reflm "TT") unq b
reflectTTQuotePattern unq (App _ f x)
  = do f' <- claimTy (sMN 0 "f") (Var (reflm "TT")) ; movelast f'
       x' <- claimTy (sMN 0 "x") (Var (reflm "TT")) ; movelast x'
       fill $ reflCall "App" [Var f', Var x']
       solve
       focus f'; reflectTTQuotePattern unq f
       focus x'; reflectTTQuotePattern unq x
reflectTTQuotePattern unq (Constant c)
  = do fill $ reflCall "TConst" [reflectConstant c]
       solve
reflectTTQuotePattern unq (Proj t i)
  = do t' <- claimTy (sMN 0 "t") (Var (reflm "TT")) ; movelast t'
       fill $ reflCall "Proj" [Var t', RConstant (I i)]
       solve
       focus t'; reflectTTQuotePattern unq t
reflectTTQuotePattern unq (Erased)
  = do erased <- claimTy (sMN 0 "erased") (Var (reflm "TT"))
       movelast erased
       fill $ (Var erased)
       solve
reflectTTQuotePattern unq (Impossible)
  = do fill $ Var (reflm "Impossible")
       solve
reflectTTQuotePattern unq (TType exp)
  = do ue <- getNameFrom (sMN 0 "uexp")
       claim ue (Var (sNS (sUN "TTUExp") ["Reflection", "Language"]))
       movelast ue
       fill $ reflCall "TType" [Var ue]
       solve
reflectTTQuotePattern unq (UType u)
  = do uH <- getNameFrom (sMN 0 "someUniv")
       claim uH (Var (reflm "Universe"))
       movelast uH
       fill $ reflCall "UType" [Var uH]
       solve
       focus uH
       fill (Var (reflm (case u of
                           NullType -> "NullType"
                           UniqueType -> "UniqueType"
                           AllTypes -> "AllTypes")))
       solve

reflectRawQuotePattern :: [Name] -> Raw -> ElabD ()
reflectRawQuotePattern unq (Var n)
  -- the unquoted names already have types, just use them
  | n `elem` unq = do fill (Var n); solve
  | otherwise = do fill (reflCall "Var" [reflectName n]); solve
reflectRawQuotePattern unq (RBind n b sc) =
  do scH <- getNameFrom (sMN 0 "sc")
     claim scH (Var (reflm "Raw"))
     movelast scH
     bH <- getNameFrom (sMN 0 "binder")
     claim bH (RApp (Var (reflm "Binder"))
                    (Var (reflm "Raw")))
     if n `elem` freeNamesR sc
        then do fill $ reflCall "RBind" [reflectName n,
                                         Var bH,
                                         Var scH]
                solve
        else do any <- getNameFrom (sMN 0 "anyName")
                claim any (Var (reflm "TTName"))
                movelast any
                fill $ reflCall "RBind" [Var any, Var bH, Var scH]
                solve
     focus scH; reflectRawQuotePattern unq sc
     focus bH; reflectBinderQuotePattern reflectRawQuotePattern (Var $ reflm "Raw") unq b
  where freeNamesR (Var n) = [n]
        freeNamesR (RBind n (Let t v) body) = concat [freeNamesR v,
                                                      freeNamesR body \\ [n],
                                                      freeNamesR t]
        freeNamesR (RBind n b body) = freeNamesR (binderTy b) ++
                                      (freeNamesR body \\ [n])
        freeNamesR (RApp f x) = freeNamesR f ++ freeNamesR x
        freeNamesR RType = []
        freeNamesR (RUType _) = []
        freeNamesR (RForce r) = freeNamesR r
        freeNamesR (RConstant _) = []
reflectRawQuotePattern unq (RApp f x) =
  do fH <- getNameFrom (sMN 0 "f")
     claim fH (Var (reflm "Raw"))
     movelast fH
     xH <- getNameFrom (sMN 0 "x")
     claim xH (Var (reflm "Raw"))
     movelast xH
     fill $ reflCall "RApp" [Var fH, Var xH]
     solve
     focus fH; reflectRawQuotePattern unq f
     focus xH; reflectRawQuotePattern unq x
reflectRawQuotePattern unq RType =
  do fill (Var (reflm "RType"))
     solve
reflectRawQuotePattern unq (RUType univ) =
  do uH <- getNameFrom (sMN 0 "universe")
     claim uH (Var (reflm "Universe"))
     movelast uH
     fill $ reflCall "RUType" [Var uH]
     solve
     focus uH; fill (reflectUniverse univ); solve
reflectRawQuotePattern unq (RForce r) =
  do rH <- getNameFrom (sMN 0 "raw")
     claim rH (Var (reflm "Raw"))
     movelast rH
     fill $ reflCall "RForce" [Var rH]
     solve
     focus rH; reflectRawQuotePattern unq r
reflectRawQuotePattern unq (RConstant c) =
  do cH <- getNameFrom (sMN 0 "const")
     claim cH (Var (reflm "Constant"))
     movelast cH
     fill (reflCall "RConstant" [Var cH]); solve
     focus cH
     fill (reflectConstant c); solve

reflectBinderQuotePattern :: ([Name] -> a -> ElabD ()) -> Raw -> [Name] -> Binder a -> ElabD ()
reflectBinderQuotePattern q ty unq (Lam t)
   = do t' <- claimTy (sMN 0 "ty") ty; movelast t'
        fill $ reflCall "Lam" [ty, Var t']
        solve
        focus t'; q unq t
reflectBinderQuotePattern q ty unq (Pi _ t k)
   = do t' <- claimTy (sMN 0 "ty") ty; movelast t'
        k' <- claimTy (sMN 0 "k") ty; movelast k';
        fill $ reflCall "Pi" [ty, Var t', Var k']
        solve
        focus t'; q unq t
reflectBinderQuotePattern q ty unq (Let x y)
   = do x' <- claimTy (sMN 0 "ty") ty; movelast x';
        y' <- claimTy (sMN 0 "v")ty; movelast y';
        fill $ reflCall "Let" [ty, Var x', Var y']
        solve
        focus x'; q unq x
        focus y'; q unq y
reflectBinderQuotePattern q ty unq (NLet x y)
   = do x' <- claimTy (sMN 0 "ty") ty; movelast x'
        y' <- claimTy (sMN 0 "v") ty; movelast y'
        fill $ reflCall "NLet" [ty, Var x', Var y']
        solve
        focus x'; q unq x
        focus y'; q unq y
reflectBinderQuotePattern q ty unq (Hole t)
   = do t' <- claimTy (sMN 0 "ty") ty; movelast t'
        fill $ reflCall "Hole" [ty, Var t']
        solve
        focus t'; q unq t
reflectBinderQuotePattern q ty unq (GHole _ t)
   = do t' <- claimTy (sMN 0 "ty") ty; movelast t'
        fill $ reflCall "GHole" [ty, Var t']
        solve
        focus t'; q unq t
reflectBinderQuotePattern q ty unq (Guess x y)
   = do x' <- claimTy (sMN 0 "ty") ty; movelast x'
        y' <- claimTy (sMN 0 "v") ty; movelast y'
        fill $ reflCall "Guess" [ty, Var x', Var y']
        solve
        focus x'; q unq x
        focus y'; q unq y
reflectBinderQuotePattern q ty unq (PVar t)
   = do t' <- claimTy (sMN 0 "ty") ty; movelast t'
        fill $ reflCall "PVar" [ty, Var t']
        solve
        focus t'; q unq t
reflectBinderQuotePattern q ty unq (PVTy t)
   = do t' <- claimTy (sMN 0 "ty") ty; movelast t'
        fill $ reflCall "PVTy" [ty, Var t']
        solve
        focus t'; q unq t

reflectUniverse :: Universe -> Raw
reflectUniverse u =
  (Var (reflm (case u of
                 NullType -> "NullType"
                 UniqueType -> "UniqueType"
                 AllTypes -> "AllTypes")))

-- | Create a reflected TT term, but leave refs to the provided name intact
reflectTTQuote :: [Name] -> Term -> Raw
reflectTTQuote unq (P nt n t)
  | n `elem` unq = Var n
  | otherwise = reflCall "P" [reflectNameType nt, reflectName n, reflectTTQuote unq t]
reflectTTQuote unq (V n)
  = reflCall "V" [RConstant (I n)]
reflectTTQuote unq (Bind n b x)
  = reflCall "Bind" [reflectName n, reflectBinderQuote reflectTTQuote (reflm "TT") unq b, reflectTTQuote unq x]
reflectTTQuote unq (App _ f x)
  = reflCall "App" [reflectTTQuote unq f, reflectTTQuote unq x]
reflectTTQuote unq (Constant c)
  = reflCall "TConst" [reflectConstant c]
reflectTTQuote unq (Proj t i)
  = reflCall "Proj" [reflectTTQuote unq t, RConstant (I i)]
reflectTTQuote unq (Erased) = Var (reflm "Erased")
reflectTTQuote unq (Impossible) = Var (reflm "Impossible")
reflectTTQuote unq (TType exp) = reflCall "TType" [reflectUExp exp]
reflectTTQuote unq (UType u) = reflCall "UType" [reflectUniverse u]

reflectRawQuote :: [Name] -> Raw -> Raw
reflectRawQuote unq (Var n)
  | n `elem` unq = Var n
  | otherwise = reflCall "Var" [reflectName n]
reflectRawQuote unq (RBind n b r) =
  reflCall "RBind" [reflectName n, reflectBinderQuote reflectRawQuote (reflm "Raw") unq b, reflectRawQuote unq r]
reflectRawQuote unq (RApp f x) =
  reflCall "RApp" [reflectRawQuote unq f, reflectRawQuote unq x]
reflectRawQuote unq RType = Var (reflm "RType")
reflectRawQuote unq (RUType u) =
  reflCall "RUType" [reflectUniverse u]
reflectRawQuote unq (RForce r) = reflCall "RForce" [reflectRawQuote unq r]
reflectRawQuote unq (RConstant cst) = reflCall "RConstant" [reflectConstant cst]

reflectNameType :: NameType -> Raw
reflectNameType (Bound) = Var (reflm "Bound")
reflectNameType (Ref) = Var (reflm "Ref")
reflectNameType (DCon x y _)
  = reflCall "DCon" [RConstant (I x), RConstant (I y)] -- FIXME: Uniqueness!
reflectNameType (TCon x y)
  = reflCall "TCon" [RConstant (I x), RConstant (I y)]

reflectName :: Name -> Raw
reflectName (UN s)
  = reflCall "UN" [RConstant (Str (str s))]
reflectName (NS n ns)
  = reflCall "NS" [ reflectName n
                  , foldr (\ n s ->
                             raw_apply ( Var $ sNS (sUN "::") ["List", "Prelude"] )
                                       [ RConstant StrType, RConstant (Str n), s ])
                             ( raw_apply ( Var $ sNS (sUN "Nil") ["List", "Prelude"] )
                                         [ RConstant StrType ])
                             (map str ns)
                  ]
reflectName (MN i n)
  = reflCall "MN" [RConstant (I i), RConstant (Str (str n))]
reflectName NErased = Var (reflm "NErased")
reflectName (SN sn) = raw_apply (Var (reflm "SN")) [reflectSpecialName sn]
reflectName (SymRef _) = error "The impossible happened: symbol table ref survived IBC loading"

reflectSpecialName :: SpecialName -> Raw
reflectSpecialName (WhereN i n1 n2) =
  reflCall "WhereN" [RConstant (I i), reflectName n1, reflectName n2]
reflectSpecialName (WithN i n) = reflCall "WithN" [ RConstant (I i)
                                                  , reflectName n
                                                  ]
reflectSpecialName (InstanceN inst ss) =
  reflCall "InstanceN" [ reflectName inst
                       , mkList (RConstant StrType) $
                           map (RConstant . Str . T.unpack) ss
                       ]
reflectSpecialName (ParentN n s) =
  reflCall "ParentN" [reflectName n, RConstant (Str (T.unpack s))]
reflectSpecialName (MethodN n) =
  reflCall "MethodN" [reflectName n]
reflectSpecialName (CaseN n) =
  reflCall "CaseN" [reflectName n]
reflectSpecialName (ElimN n) =
  reflCall "ElimN" [reflectName n]
reflectSpecialName (InstanceCtorN n) =
  reflCall "InstanceCtorN" [reflectName n]
reflectSpecialName (MetaN parent meta) =
  reflCall "MetaN" [reflectName parent, reflectName meta]

-- | Elaborate a name to a pattern.  This means that NS and UN will be intact.
-- MNs corresponding to will care about the string but not the number.  All
-- others become _.
reflectNameQuotePattern :: Name -> ElabD ()
reflectNameQuotePattern n@(UN s)
  = do fill $ reflectName n
       solve
reflectNameQuotePattern n@(NS _ _)
  = do fill $ reflectName n
       solve
reflectNameQuotePattern (MN _ n)
  = do i <- getNameFrom (sMN 0 "mnCounter")
       claim i (RConstant (AType (ATInt ITNative)))
       movelast i
       fill $ reflCall "MN" [Var i, RConstant (Str $ T.unpack n)]
       solve
reflectNameQuotePattern _ -- for all other names, match any
  = do nameHole <- getNameFrom (sMN 0 "name")
       claim nameHole (Var (reflm "TTName"))
       movelast nameHole
       fill (Var nameHole)
       solve

reflectBinder :: Binder Term -> Raw
reflectBinder = reflectBinderQuote reflectTTQuote (reflm "TT") []

reflectBinderQuote :: ([Name] -> a -> Raw) -> Name -> [Name] -> Binder a -> Raw
reflectBinderQuote q ty unq (Lam t)
   = reflCall "Lam" [Var ty, q unq t]
reflectBinderQuote q ty unq (Pi _ t k)
   = reflCall "Pi" [Var ty, q unq t, q unq k]
reflectBinderQuote q ty unq (Let x y)
   = reflCall "Let" [Var ty, q unq x, q unq y]
reflectBinderQuote q ty unq (NLet x y)
   = reflCall "NLet" [Var ty, q unq x, q unq y]
reflectBinderQuote q ty unq (Hole t)
   = reflCall "Hole" [Var ty, q unq t]
reflectBinderQuote q ty unq (GHole _ t)
   = reflCall "GHole" [Var ty, q unq t]
reflectBinderQuote q ty unq (Guess x y)
   = reflCall "Guess" [Var ty, q unq x, q unq y]
reflectBinderQuote q ty unq (PVar t)
   = reflCall "PVar" [Var ty, q unq t]
reflectBinderQuote q ty unq (PVTy t)
   = reflCall "PVTy" [Var ty, q unq t]

mkList :: Raw -> [Raw] -> Raw
mkList ty []      = RApp (Var (sNS (sUN "Nil") ["List", "Prelude"])) ty
mkList ty (x:xs) = RApp (RApp (RApp (Var (sNS (sUN "::") ["List", "Prelude"])) ty)
                              x)
                        (mkList ty xs)

reflectConstant :: Const -> Raw
reflectConstant c@(I  _) = reflCall "I"  [RConstant c]
reflectConstant c@(BI _) = reflCall "BI" [RConstant c]
reflectConstant c@(Fl _) = reflCall "Fl" [RConstant c]
reflectConstant c@(Ch _) = reflCall "Ch" [RConstant c]
reflectConstant c@(Str _) = reflCall "Str" [RConstant c]
reflectConstant c@(B8 _) = reflCall "B8" [RConstant c]
reflectConstant c@(B16 _) = reflCall "B16" [RConstant c]
reflectConstant c@(B32 _) = reflCall "B32" [RConstant c]
reflectConstant c@(B64 _) = reflCall "B64" [RConstant c]
reflectConstant (AType (ATInt ITNative)) = reflCall "AType" [reflCall "ATInt" [Var (reflm "ITNative")]]
reflectConstant (AType (ATInt ITBig)) = reflCall "AType" [reflCall "ATInt" [Var (reflm "ITBig")]]
reflectConstant (AType ATFloat) = reflCall "AType" [Var (reflm "ATFloat")]
reflectConstant (AType (ATInt ITChar)) = reflCall "AType" [reflCall "ATInt" [Var (reflm "ITChar")]]
reflectConstant StrType = Var (reflm "StrType")
reflectConstant (AType (ATInt (ITFixed IT8)))  = reflCall "AType" [reflCall "ATInt" [reflCall "ITFixed" [Var (reflm "IT8")]]]
reflectConstant (AType (ATInt (ITFixed IT16))) = reflCall "AType" [reflCall "ATInt" [reflCall "ITFixed" [Var (reflm "IT16")]]]
reflectConstant (AType (ATInt (ITFixed IT32))) = reflCall "AType" [reflCall "ATInt" [reflCall "ITFixed" [Var (reflm "IT32")]]]
reflectConstant (AType (ATInt (ITFixed IT64))) = reflCall "AType" [reflCall "ATInt" [reflCall "ITFixed" [Var (reflm "IT64")]]]
reflectConstant VoidType = Var (reflm "VoidType")
reflectConstant Forgot = Var (reflm "Forgot")
reflectConstant WorldType = Var (reflm "WorldType")
reflectConstant TheWorld = Var (reflm "TheWorld")

reflectUExp :: UExp -> Raw
reflectUExp (UVar i) = reflCall "UVar" [RConstant (I i)]
reflectUExp (UVal i) = reflCall "UVal" [RConstant (I i)]

-- | Reflect the environment of a proof into a List (TTName, Binder TT)
reflectEnv :: Env -> Raw
reflectEnv = foldr consToEnvList emptyEnvList
  where
    consToEnvList :: (Name, Binder Term) -> Raw -> Raw
    consToEnvList (n, b) l
      = raw_apply (Var (sNS (sUN "::") ["List", "Prelude"]))
                  [ envTupleType
                  , raw_apply (Var pairCon) [ (Var $ reflm "TTName")
                                            , (RApp (Var $ reflm "Binder")
                                                    (Var $ reflm "TT"))
                                            , reflectName n
                                            , reflectBinder b
                                            ]
                  , l
                  ]

    emptyEnvList :: Raw
    emptyEnvList = raw_apply (Var (sNS (sUN "Nil") ["List", "Prelude"]))
                             [envTupleType]

-- | Reflect an error into the internal datatype of Idris -- TODO
rawBool :: Bool -> Raw
rawBool True  = Var (sNS (sUN "True") ["Bool", "Prelude"])
rawBool False = Var (sNS (sUN "False") ["Bool", "Prelude"])

rawNil :: Raw -> Raw
rawNil ty = raw_apply (Var (sNS (sUN "Nil") ["List", "Prelude"])) [ty]

rawCons :: Raw -> Raw -> Raw -> Raw
rawCons ty hd tl = raw_apply (Var (sNS (sUN "::") ["List", "Prelude"])) [ty, hd, tl]

rawList :: Raw -> [Raw] -> Raw
rawList ty = foldr (rawCons ty) (rawNil ty)

rawPairTy :: Raw -> Raw -> Raw
rawPairTy t1 t2 = raw_apply (Var pairTy) [t1, t2]

rawPair :: (Raw, Raw) -> (Raw, Raw) -> Raw
rawPair (a, b) (x, y) = raw_apply (Var pairCon) [a, b, x, y]

-- | Idris tuples nest to the right
rawTripleTy :: Raw -> Raw -> Raw -> Raw
rawTripleTy a b c = rawPairTy a (rawPairTy b c)

rawTriple :: (Raw, Raw, Raw) -> (Raw, Raw, Raw) -> Raw
rawTriple (a, b, c) (x, y, z) = rawPair (a, rawPairTy b c) (x, rawPair (b, c) (y, z))

reflectCtxt :: [(Name, Type)] -> Raw
reflectCtxt ctxt = rawList (rawPairTy  (Var $ reflm "TTName") (Var $ reflm "TT"))
                           (map (\ (n, t) -> (rawPair (Var $ reflm "TTName", Var $ reflm "TT")
                                                      (reflectName n, reflect t)))
                                ctxt)

reflectErr :: Err -> Raw
reflectErr (Msg msg) = raw_apply (Var $ reflErrName "Msg") [RConstant (Str msg)]
reflectErr (InternalMsg msg) = raw_apply (Var $ reflErrName "InternalMsg") [RConstant (Str msg)]
reflectErr (CantUnify b (t1,_) (t2,_) e ctxt i) =
  raw_apply (Var $ reflErrName "CantUnify")
            [ rawBool b
            , reflect t1
            , reflect t2
            , reflectErr e
            , reflectCtxt ctxt
            , RConstant (I i)]
reflectErr (InfiniteUnify n tm ctxt) =
  raw_apply (Var $ reflErrName "InfiniteUnify")
            [ reflectName n
            , reflect tm
            , reflectCtxt ctxt
            ]
reflectErr (CantConvert t t' ctxt) =
  raw_apply (Var $ reflErrName "CantConvert")
            [ reflect t
            , reflect t'
            , reflectCtxt ctxt
            ]
reflectErr (CantSolveGoal t ctxt) =
  raw_apply (Var $ reflErrName "CantSolveGoal")
            [ reflect t
            , reflectCtxt ctxt
            ]
reflectErr (UnifyScope n n' t ctxt) =
  raw_apply (Var $ reflErrName "UnifyScope")
            [ reflectName n
            , reflectName n'
            , reflect t
            , reflectCtxt ctxt
            ]
reflectErr (CantInferType str) =
  raw_apply (Var $ reflErrName "CantInferType") [RConstant (Str str)]
reflectErr (NonFunctionType t t') =
  raw_apply (Var $ reflErrName "NonFunctionType") [reflect t, reflect t']
reflectErr (NotEquality t t') =
  raw_apply (Var $ reflErrName "NotEquality") [reflect t, reflect t']
reflectErr (TooManyArguments n) = raw_apply (Var $ reflErrName "TooManyArguments") [reflectName n]
reflectErr (CantIntroduce t) = raw_apply (Var $ reflErrName "CantIntroduce") [reflect t]
reflectErr (NoSuchVariable n) = raw_apply (Var $ reflErrName "NoSuchVariable") [reflectName n]
reflectErr (WithFnType t) = raw_apply (Var $ reflErrName "WithFnType") [reflect t]
reflectErr (CantMatch t) = raw_apply (Var $ reflErrName "CantMatch") [reflect t]
reflectErr (NoTypeDecl n) = raw_apply (Var $ reflErrName "NoTypeDecl") [reflectName n]
reflectErr (NotInjective t1 t2 t3) =
  raw_apply (Var $ reflErrName "NotInjective")
            [ reflect t1
            , reflect t2
            , reflect t3
            ]
reflectErr (CantResolve _ t) = raw_apply (Var $ reflErrName "CantResolve") [reflect t]
reflectErr (InvalidTCArg n t) = raw_apply (Var $ reflErrName "InvalidTCArg") [reflectName n, reflect t]
reflectErr (CantResolveAlts ss) =
  raw_apply (Var $ reflErrName "CantResolveAlts")
            [rawList (Var $ reflm "TTName") (map reflectName ss)]
reflectErr (IncompleteTerm t) = raw_apply (Var $ reflErrName "IncompleteTerm") [reflect t]
reflectErr (NoEliminator str t) 
  = raw_apply (Var $ reflErrName "NoEliminator") [RConstant (Str str),
                                                  reflect t]
reflectErr (UniverseError fc ue old new tys) =
  -- NB: loses information, but OK because this is not likely to be rewritten
  Var $ reflErrName "UniverseError"
reflectErr ProgramLineComment = Var $ reflErrName "ProgramLineComment"
reflectErr (Inaccessible n) = raw_apply (Var $ reflErrName "Inaccessible") [reflectName n]
reflectErr (UnknownImplicit n f) = raw_apply (Var $ reflErrName "UnknownImplicit") [reflectName n, reflectName f]
reflectErr (NonCollapsiblePostulate n) = raw_apply (Var $ reflErrName "NonCollabsiblePostulate") [reflectName n]
reflectErr (AlreadyDefined n) = raw_apply (Var $ reflErrName "AlreadyDefined") [reflectName n]
reflectErr (ProofSearchFail e) = raw_apply (Var $ reflErrName "ProofSearchFail") [reflectErr e]
reflectErr (NoRewriting tm) = raw_apply (Var $ reflErrName "NoRewriting") [reflect tm]
reflectErr (ProviderError str) =
  raw_apply (Var $ reflErrName "ProviderError") [RConstant (Str str)]
reflectErr (LoadingFailed str err) =
  raw_apply (Var $ reflErrName "LoadingFailed") [RConstant (Str str)]
reflectErr x = raw_apply (Var (sNS (sUN "Msg") ["Errors", "Reflection", "Language"])) [RConstant . Str $ "Default reflection: " ++ show x]

-- | Reflect a file context
reflectFC :: FC -> Raw
reflectFC fc = raw_apply (Var (reflm "FileLoc"))
                         [ RConstant (Str (fc_fname fc))
                         , raw_apply (Var pairCon) $
                             [intTy, intTy] ++
                             map (RConstant . I)
                                 [ fst (fc_start fc)
                                 , snd (fc_start fc)
                                 ]
                         , raw_apply (Var pairCon) $
                             [intTy, intTy] ++
                             map (RConstant . I)
                                 [ fst (fc_end fc)
                                 , snd (fc_end fc)
                                 ]
                         ]
  where intTy = RConstant (AType (ATInt ITNative))

fromTTMaybe :: Term -> Maybe Term -- WARNING: Assumes the term has type Maybe a
fromTTMaybe (App _ (App _ (P (DCon _ _ _) (NS (UN just) _) _) ty) tm)
  | just == txt "Just" = Just tm
fromTTMaybe x          = Nothing

reflErrName :: String -> Name
reflErrName n = sNS (sUN n) ["Errors", "Reflection", "Language"]

-- | Attempt to reify a report part from TT to the internal
-- representation. Not in Idris or ElabD monads because it should be usable
-- from either.
reifyReportPart :: Term -> Either Err ErrorReportPart
reifyReportPart (App _ (P (DCon _ _ _) n _) (Constant (Str msg))) | n == reflm "TextPart" =
    Right (TextPart msg)
reifyReportPart (App _ (P (DCon _ _ _) n _) ttn)
  | n == reflm "NamePart" =
    case runElab initEState (reifyTTName ttn) (initElaborator NErased initContext emptyContext Erased) of
      Error e -> Left . InternalMsg $
       "could not reify name term " ++
       show ttn ++
       " when reflecting an error:" ++ show e
      OK (n', _)-> Right $ NamePart n'
reifyReportPart (App _ (P (DCon _ _ _) n _) tm)
  | n == reflm "TermPart" =
  case runElab initEState (reifyTT tm) (initElaborator NErased initContext emptyContext Erased) of
    Error e -> Left . InternalMsg $
      "could not reify reflected term " ++
      show tm ++
      " when reflecting an error:" ++ show e
    OK (tm', _) -> Right $ TermPart tm'
reifyReportPart (App _ (P (DCon _ _ _) n _) tm)
  | n == reflm "RawPart" =
  case runElab initEState (reifyRaw tm) (initElaborator NErased initContext emptyContext Erased) of
    Error e -> Left . InternalMsg $
      "could not reify reflected raw term " ++
      show tm ++
      " when reflecting an error: " ++ show e
    OK (tm', _) -> Right $ RawPart tm'
reifyReportPart (App _ (P (DCon _ _ _) n _) tm)
  | n == reflm "SubReport" =
  case unList tm of
    Just xs -> do subParts <- mapM reifyReportPart xs
                  Right (SubReport subParts)
    Nothing -> Left . InternalMsg $ "could not reify subreport " ++ show tm
reifyReportPart x = Left . InternalMsg $ "could not reify " ++ show x

reifyErasure :: Term -> ElabD RErasure
reifyErasure (P (DCon _ _ _) n _)
  | n == tacN "Erased" = return RErased
  | n == tacN "NotErased" = return RNotErased
reifyErasure tm = fail $ "Can't reify " ++ show tm ++ " as erasure info."

reifyTyDecl :: Term -> ElabD RTyDecl
reifyTyDecl (App _ (App _ (App _ (P (DCon _ _ _) n _) tyN) args) ret)
  | n == tacN "Declare" =
  do tyN'  <- reifyTTName tyN
     args' <- case unList args of
                Nothing -> fail $ "Couldn't reify " ++ show args ++ " as an arglist."
                Just xs -> mapM reifyRArg xs
     ret'  <- reifyRaw ret
     return $ RDeclare tyN' args' ret'
  where reifyRArg :: Term -> ElabD RArg
        reifyRArg (App _ (App _ (App _ (P (DCon _ _ _) n _) argN) argE) argTy)
          | n == tacN "Explicit"   = liftM3 RExplicit
                                            (reifyTTName argN)
                                            (reifyErasure argE)
                                            (reifyRaw argTy)
          | n == tacN "Implicit"   = liftM3 RImplicit
                                            (reifyTTName argN)
                                            (reifyErasure argE)
                                            (reifyRaw argTy)                                  | n == tacN "Constraint" = liftM3 RConstraint
                                            (reifyTTName argN)
                                            (reifyErasure argE)
                                            (reifyRaw argTy)
        reifyRArg aTm = fail $ "Couldn't reify " ++ show aTm ++ " as an RArg."
reifyTyDecl tm = fail $ "Couldn't reify " ++ show tm ++ " as a type declaration."

reifyFunDefn :: Term -> ElabD RFunDefn
reifyFunDefn (App _ (App _ (P _ n _) fnN) clauses)
  | n == tacN "DefineFun" =
  do fnN' <- reifyTTName fnN
     clauses' <- case unList clauses of
                   Nothing -> fail $ "Couldn't reify " ++ show clauses ++ " as a clause list"
                   Just cs -> mapM reifyC cs
     return $ RDefineFun fnN' clauses'
  where reifyC :: Term -> ElabD RFunClause
        reifyC (App _ (App _ (P (DCon _ _ _) n _) lhs) rhs)
          | n == tacN "MkFunClause" = liftM2 RMkFunClause
                                             (reifyRaw lhs)
                                             (reifyRaw rhs)
        reifyC (App _ (P (DCon _ _ _) n _) lhs)
          | n == tacN "MkImpossibleClause" = fmap RMkImpossibleClause $ reifyRaw lhs
        reifyC tm = fail $ "Couldn't reify " ++ show tm ++ " as a clause."
reifyFunDefn tm = fail $ "Couldn't reify " ++ show tm ++ " as a function declaration."

envTupleType :: Raw
envTupleType
  = raw_apply (Var pairTy) [ (Var $ reflm "TTName")
                           , (RApp (Var $ reflm "Binder") (Var $ reflm "TT"))
                           ]

-- | Apply Idris's implicit info to get a signature. The [PArg] should
-- come from a lookup in idris_implicits on IState.
getArgs :: [PArg] -> Raw -> ([RArg], Raw)
getArgs []     r = ([], r)
getArgs (a:as) (RBind n (Pi _ ty _) sc) =
  let (args, res) = getArgs as sc
      erased = if InaccessibleArg `elem` argopts a then RErased else RNotErased
      arg' = case a of
               PImp {} -> RImplicit n erased ty
               PExp {} -> RExplicit n erased ty
               PConstraint {} -> RConstraint n erased ty
               PTacImplicit {} -> RImplicit n erased ty -- TODO?
  in (arg':args, res)
getArgs _ r = ([], r)

-- | Build the reflected datatype definition(s) that correspond(s) to
-- a provided unqualified name
buildDatatypes :: IState -> Name -> [RDatatype]
buildDatatypes ist n =
  catMaybes [ mkDataType dn ti
            | (dn, ti) <- lookupCtxtName n datatypes
            ]
  where datatypes = idris_datatypes ist
        ctxt      = tt_ctxt ist
        impls     = idris_implicits ist

        ctorSig cn = do cty <- fmap forget (lookupTyExact cn ctxt)
                        argInfo <- lookupCtxtExact cn impls
                        let (args, res) = getArgs argInfo cty
                        return (cn, args, res)

        mkDataType name (TI {param_pos = params, con_names = constrs}) =
          do (TyDecl (TCon _ _) ty) <- lookupDefExact name ctxt
             implInfo <- lookupCtxtExact name impls
             let (tcargs, tcres) = getTCArgs params implInfo (forget ty) 0
             ctors <- mapM ctorSig constrs
             return $ RDatatype name tcargs tcres ctors

        getTCArgs params implInfo (RBind an (Pi _ ty _) body) i =
          let (erased, implInfo') = case implInfo of
                                      [] -> (RNotErased, [])
                                      (a:as) -> (if InaccessibleArg `elem` argopts a
                                                    then RErased
                                                    else RNotErased,
                                                 as)
              (args, res) = getTCArgs params implInfo' body (i+1)
          in if i `elem` params
               then (RParameter an erased ty : args, res )
               else (RIndex an erased ty : args, res)
        getTCArgs _ implInfo tm _ = ([], tm)

reflectErasure :: RErasure -> Raw
reflectErasure RErased    = Var (tacN "Erased")
reflectErasure RNotErased = Var (tacN "NotErased")

reflectArg :: RArg -> Raw
reflectArg arg =
   RApp (RApp (RApp (Var con) (reflectName $ argName arg))
              (reflectErasure $ argErased arg))
        (reflectRaw $ argTy arg)
   where con = case arg of
                 RExplicit{}   -> tacN "Explicit"
                 RImplicit{}   -> tacN "Implicit"
                 RConstraint{} -> tacN "Constraint"

reflectDatatype :: RDatatype -> Raw
reflectDatatype (RDatatype tyn tyConArgs tyConRes constrs) =
  raw_apply (Var $ tacN "MkDatatype") [ reflectName tyn
                                      , rawList (Var $ tacN "TyConArg") (map reflectConArg tyConArgs)
                                      , reflectRaw tyConRes
                                      , rawList (rawTripleTy (Var $ reflm "TTName")
                                                             (RApp (Var (sNS (sUN "List") ["List", "Prelude"])) (Var $ tacN "Arg"))
                                                             (Var $ reflm "Raw"))
                                                [ rawTriple ((Var $ reflm "TTName"),
                                                             (RApp (Var (sNS (sUN "List") ["List", "Prelude"])) (Var $ tacN "Arg")),
                                                             (Var $ reflm "Raw"))
                                                            (reflectName cn,
                                                             rawList (Var $ tacN "Arg") (map reflectArg cargs),
                                                             reflectRaw cty)
                                                | (cn, cargs, cty) <- constrs
                                                ]
                                      ]
  where reflectConArg (RParameter n e t) =
          raw_apply (Var $ tacN "Parameter") [reflectName n, reflectErasure e, reflectRaw t]
        reflectConArg (RIndex n e t) =
          raw_apply (Var $ tacN "Index")     [reflectName n, reflectErasure e, reflectRaw t]

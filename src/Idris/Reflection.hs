{-|
Module      : Idris.Reflection
Description : Code related to Idris's reflection system. This module contains quoters and unquoters along with some supporting datatypes.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE CPP, PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -fwarn-unused-imports #-}
module Idris.Reflection where

import Idris.Core.Elaborate (claim, fill, focus, getNameFrom, initElaborator,
                             movelast, runElab, solve)
import Idris.Core.Evaluate (Def(TyDecl), initContext, lookupDefExact,
                            lookupTyExact)
import Idris.Core.TT

import Idris.AbsSyntaxTree (ArgOpt(..), ElabD, Fixity(..), IState(idris_datatypes, idris_implicits, idris_patdefs, tt_ctxt),
                            PArg, PArg'(..), PTactic, PTactic'(..), PTerm(..),
                            initEState, pairCon, pairTy)
import Idris.Delaborate (delab)

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative (pure, (<$>), (<*>))
import Data.Traversable (mapM)
import Prelude hiding (mapM)
#endif
import Control.Monad (liftM, liftM2, liftM4)
import Control.Monad.State.Strict (lift)
import Data.List (findIndex, (\\))
import Data.Maybe (catMaybes)
import qualified Data.Text as T

data RErasure = RErased | RNotErased deriving Show

data RPlicity = RExplicit | RImplicit | RConstraint deriving Show

data RFunArg = RFunArg { argName    :: Name
                       , argTy      :: Raw
                       , argPlicity :: RPlicity
                       , erasure    :: RErasure
                       }
  deriving Show

data RTyDecl = RDeclare Name [RFunArg] Raw deriving Show

data RTyConArg = RParameter RFunArg
               | RIndex     RFunArg
  deriving Show

data RCtorArg = RCtorParameter RFunArg | RCtorField RFunArg deriving Show

data RDatatype = RDatatype Name [RTyConArg] Raw [(Name, [RCtorArg], Raw)] deriving Show

data RConstructorDefn = RConstructor Name [RFunArg] Raw

data RDataDefn = RDefineDatatype Name [RConstructorDefn]

rArgOpts :: RErasure -> [ArgOpt]
rArgOpts RErased = [InaccessibleArg]
rArgOpts _ = []

rFunArgToPArg :: RFunArg -> PArg
rFunArgToPArg (RFunArg n _ RExplicit e) = PExp 0 (rArgOpts e) n Placeholder
rFunArgToPArg (RFunArg n _ RImplicit e) = PImp 0 False (rArgOpts e) n Placeholder
rFunArgToPArg (RFunArg n _ RConstraint e) = PConstraint 0 (rArgOpts e) n Placeholder

data RFunClause a = RMkFunClause a a
                  | RMkImpossibleClause a
                  deriving Show

data RFunDefn a = RDefineFun Name [RFunClause a] deriving Show

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
reify _ (P _ n _) | n == reflm "Implementation" = return TCImplementation
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
           | t == reflm "Search" = return (ProofSearch True True i Nothing [] [])
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
        | n == reflm "Erased" = return Erased
reifyTT t@(P _ n _)
        | n == reflm "Impossible" = return Impossible
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
         | n == reflm "RType" = return RType
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
                | t == reflm "ImplementationN" =
                  case unList ss of
                    Nothing -> fail "Can't reify ImplementationN strings"
                    Just ss' -> ImplementationN <$> reifyTTName n <*>
                                 pure [T.pack s | Constant (Str s) <- ss']
        reifySN t [n, Constant (Str s)]
                | t == reflm "ParentN" =
                  ParentN <$> reifyTTName n <*> pure (T.pack s)
        reifySN t [n]
                | t == reflm "MethodN" =
                  MethodN <$> reifyTTName n
        reifySN t [fc, n]
                | t == reflm "CaseN" =
                  CaseN <$> (FC' <$> reifyFC fc) <*> reifyTTName n
        reifySN t [n]
                | t == reflm "ElimN" =
                  ElimN <$> reifyTTName n
        reifySN t [n]
                | t == reflm "ImplementationCtorN" =
                  ImplementationCtorN <$> reifyTTName n
        reifySN t [n1, n2]
                | t == reflm "MetaN" =
                  MetaN <$> reifyTTName n1 <*> reifyTTName n2
        reifySN t args = fail $ "Can't reify special name " ++ show t ++ show args
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
                      | f == reflm "Lam" = liftM (Lam RigW) (reif t)
reifyTTBinderApp reif f [t, k]
                      | f == reflm "Pi" = liftM2 (Pi RigW Nothing) (reif t) (reif k)
reifyTTBinderApp reif f [x, y]
                      | f == reflm "Let" = liftM2 Let (reif x) (reif y)
reifyTTBinderApp reif f [t]
                      | f == reflm "Hole" = liftM Hole (reif t)
reifyTTBinderApp reif f [t]
                      | f == reflm "GHole" = liftM (GHole 0 []) (reif t)
reifyTTBinderApp reif f [x, y]
                      | f == reflm "Guess" = liftM2 Guess (reif x) (reif y)
reifyTTBinderApp reif f [t]
                      | f == reflm "PVar" = liftM (PVar RigW) (reif t)
reifyTTBinderApp reif f [t]
                      | f == reflm "PVTy" = liftM PVTy (reif t)
reifyTTBinderApp _ f args = fail ("Unknown reflection binder: " ++ show (f, args))

reifyTTConst :: Term -> ElabD Const
reifyTTConst (P _ n _) | n == reflm "StrType"  = return StrType
reifyTTConst (P _ n _) | n == reflm "VoidType" = return VoidType
reifyTTConst (P _ n _) | n == reflm "Forgot"   = return Forgot
reifyTTConst t@(App _ _ _)
             | (P _ f _, [arg]) <- unApply t   = reifyTTConstApp f arg
reifyTTConst t = fail ("Unknown reflection constant: " ++ show t)

reifyTTConstApp :: Name -> Term -> ElabD Const
reifyTTConstApp f aty
                | f == reflm "AType" = fmap AType (reifyArithTy aty)
reifyTTConstApp f (Constant c@(I _))
                | f == reflm "I"   = return c
reifyTTConstApp f (Constant c@(BI _))
                | f == reflm "BI"  = return c
reifyTTConstApp f (Constant c@(Fl _))
                | f == reflm "Fl"  = return c
reifyTTConstApp f (Constant c@(Ch _))
                | f == reflm "Ch"  = return c
reifyTTConstApp f (Constant c@(Str _))
                | f == reflm "Str" = return c
reifyTTConstApp f (Constant c@(B8 _))
                | f == reflm "B8"  = return c
reifyTTConstApp f (Constant c@(B16 _))
                | f == reflm "B16" = return c
reifyTTConstApp f (Constant c@(B32 _))
                | f == reflm "B32" = return c
reifyTTConstApp f (Constant c@(B64 _))
                | f == reflm "B64" = return c
reifyTTConstApp f v@(P _ _ _) =
    lift . tfail . Msg $
      "Can't reify the variable " ++
      show v ++
      " as a constant, because its value is not statically known."
reifyTTConstApp f arg = fail ("Unknown reflection constant: " ++ show (f, arg))

reifyArithTy :: Term -> ElabD ArithTy
reifyArithTy (App _ (P _ n _) intTy) | n == reflm "ATInt"    = fmap ATInt (reifyIntTy intTy)
reifyArithTy (P _ n _)               | n == reflm "ATDouble" = return ATFloat
reifyArithTy x = fail ("Couldn't reify reflected ArithTy: " ++ show x)

reifyNativeTy :: Term -> ElabD NativeTy
reifyNativeTy (P _ n _) | n == reflm "IT8"  = return IT8
reifyNativeTy (P _ n _) | n == reflm "IT16" = return IT16
reifyNativeTy (P _ n _) | n == reflm "IT32" = return IT32
reifyNativeTy (P _ n _) | n == reflm "IT64" = return IT64
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
      (P _ f _, [Constant (Str str), Constant (I i)])
           | f == reflm "UVar" -> return $ UVar str i
      (P _ f _, [Constant (I i)])
           | f == reflm "UVal" -> return $ UVal i
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

intToReflectedNat :: Int -> Raw
intToReflectedNat i = if i <= 0
                        then Var (natN "Z")
                        else RApp (Var (natN "S")) (intToReflectedNat (i - 1))
  where natN :: String -> Name
        natN n = sNS (sUN n) ["Nat", "Prelude"]

reflectFixity :: Fixity -> Raw
reflectFixity (Infixl  p) = RApp (Var (tacN "Infixl")) (intToReflectedNat p)
reflectFixity (Infixr  p) = RApp (Var (tacN "Infixr")) (intToReflectedNat p)
reflectFixity (InfixN  p) = RApp (Var (tacN "InfixN")) (intToReflectedNat p)
reflectFixity (PrefixN p) = RApp (Var (tacN "PrefixN")) (intToReflectedNat p)

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
  = lift . tfail . InternalMsg $
      "Phase error! The Proj constructor is for optimization only and should not have been reflected during elaboration."
reflectTTQuotePattern unq Erased
  = do erased <- claimTy (sMN 0 "erased") (Var (reflm "TT"))
       movelast erased
       fill (Var erased)
reflectTTQuotePattern unq Impossible
  = lift . tfail . InternalMsg $
      "Phase error! The Impossible constructor is for optimization only and should not have been reflected during elaboration."
reflectTTQuotePattern unq (Inferred t)
  = lift . tfail . InternalMsg $
      "Phase error! The Inferred constructor is for coverage checking only and should not have been reflected during elaboration."
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
reflectRawQuotePattern unq (RConstant c) =
  do cH <- getNameFrom (sMN 0 "const")
     claim cH (Var (reflm "Constant"))
     movelast cH
     fill (reflCall "RConstant" [Var cH]); solve
     focus cH
     fill (reflectConstant c); solve

reflectBinderQuotePattern :: ([Name] -> a -> ElabD ()) -> Raw -> [Name] -> Binder a -> ElabD ()
reflectBinderQuotePattern q ty unq (Lam _ t)
   = do t' <- claimTy (sMN 0 "ty") ty; movelast t'
        fill $ reflCall "Lam" [ty, Var t']
        solve
        focus t'; q unq t
reflectBinderQuotePattern q ty unq (Pi _ _ t k)
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
        fill $ reflCall "Let" [ty, Var x', Var y']
        solve
        focus x'; q unq x
        focus y'; q unq y
reflectBinderQuotePattern q ty unq (Hole t)
   = do t' <- claimTy (sMN 0 "ty") ty; movelast t'
        fill $ reflCall "Hole" [ty, Var t']
        solve
        focus t'; q unq t
reflectBinderQuotePattern q ty unq (GHole _ _ t)
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
reflectBinderQuotePattern q ty unq (PVar _ t)
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
reflectTTQuote unq (TType exp) = reflCall "TType" [reflectUExp exp]
reflectTTQuote unq (UType u) = reflCall "UType" [reflectUniverse u]
reflectTTQuote _   (Proj _ _) =
  error "Phase error! The Proj constructor is for optimization only and should not have been reflected during elaboration."
reflectTTQuote unq Erased = Var (reflm "Erased")
reflectTTQuote _   Impossible =
  error "Phase error! The Impossible constructor is for optimization only and should not have been reflected during elaboration."
reflectTTQuote _   (Inferred tm) =
  error "Phase error! The Inferred constructor is for coverage checking only and should not have been reflected during elaboration."

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
reflectName (SN sn) = raw_apply (Var (reflm "SN")) [reflectSpecialName sn]
reflectName (SymRef _) = error "The impossible happened: symbol table ref survived IBC loading"

reflectSpecialName :: SpecialName -> Raw
reflectSpecialName (WhereN i n1 n2) =
  reflCall "WhereN" [RConstant (I i), reflectName n1, reflectName n2]
reflectSpecialName (WithN i n) = reflCall "WithN" [ RConstant (I i)
                                                  , reflectName n
                                                  ]
reflectSpecialName (ImplementationN impl ss) =
  reflCall "ImplementationN" [ reflectName impl
                             , mkList (RConstant StrType) $
                                 map (RConstant . Str . T.unpack) ss
                             ]
reflectSpecialName (ParentN n s) =
  reflCall "ParentN" [reflectName n, RConstant (Str (T.unpack s))]
reflectSpecialName (MethodN n) =
  reflCall "MethodN" [reflectName n]
reflectSpecialName (CaseN fc n) =
  reflCall "CaseN" [reflectFC (unwrapFC fc), reflectName n]
reflectSpecialName (ElimN n) =
  reflCall "ElimN" [reflectName n]
reflectSpecialName (ImplementationCtorN n) =
  reflCall "ImplementationCtorN" [reflectName n]
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
reflectBinderQuote q ty unq (Lam _ t)
   = reflCall "Lam" [Var ty, q unq t]
reflectBinderQuote q ty unq (Pi _ _ t k)
   = reflCall "Pi" [Var ty, q unq t, q unq k]
reflectBinderQuote q ty unq (Let x y)
   = reflCall "Let" [Var ty, q unq x, q unq y]
reflectBinderQuote q ty unq (NLet x y)
   = reflCall "Let" [Var ty, q unq x, q unq y]
reflectBinderQuote q ty unq (Hole t)
   = reflCall "Hole" [Var ty, q unq t]
reflectBinderQuote q ty unq (GHole _ _ t)
   = reflCall "GHole" [Var ty, q unq t]
reflectBinderQuote q ty unq (Guess x y)
   = reflCall "Guess" [Var ty, q unq x, q unq y]
reflectBinderQuote q ty unq (PVar _ t)
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
reflectConstant (AType ATFloat) = reflCall "AType" [Var (reflm "ATDouble")]
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
reflectUExp (UVar ns i) = reflCall "UVar" [RConstant (Str ns), RConstant (I i)]
reflectUExp (UVal i) = reflCall "UVal" [RConstant (I i)]

-- | Reflect the environment of a proof into a List (TTName, Binder TT)
reflectEnv :: Env -> Raw
reflectEnv = foldr consToEnvList emptyEnvList . envBinders
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

-- Reflected environments don't get the RigCount (for the moment, at least)
reifyEnv :: Term -> ElabD Env
reifyEnv tm = do preEnv <- reifyList (reifyPair reifyTTName (reifyTTBinder reifyTT (reflm "TT"))) tm
                 return $ map (\(n, b) -> (n, RigW, b)) preEnv

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
reflectErr (CantResolve _ t more)
   = raw_apply (Var $ reflErrName "CantResolve") [reflect t, reflectErr more]
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
reflectErr (NoRewriting l r tm) = raw_apply (Var $ reflErrName "NoRewriting") [reflect l, reflect r, reflect tm]
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

reifyFC :: Term -> ElabD FC
reifyFC tm
  | (P (DCon _ _ _) cn _, [Constant (Str fn), st, end]) <- unApply tm
  , cn == reflm "FileLoc" = FC fn <$> reifyPair reifyInt reifyInt st <*> reifyPair reifyInt reifyInt end
  | otherwise = fail $ "Not a source location: " ++ show tm

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
    case runElab initEState (reifyTTName ttn) (initElaborator (sMN 0 "hole") internalNS initContext emptyContext 0 Erased) of
      Error e -> Left . InternalMsg $
       "could not reify name term " ++
       show ttn ++
       " when reflecting an error:" ++ show e
      OK (n', _)-> Right $ NamePart n'
reifyReportPart (App _ (P (DCon _ _ _) n _) tm)
  | n == reflm "TermPart" =
  case runElab initEState (reifyTT tm) (initElaborator (sMN 0 "hole") internalNS initContext emptyContext 0 Erased) of
    Error e -> Left . InternalMsg $
      "could not reify reflected term " ++
      show tm ++
      " when reflecting an error:" ++ show e
    OK (tm', _) -> Right $ TermPart tm'
reifyReportPart (App _ (P (DCon _ _ _) n _) tm)
  | n == reflm "RawPart" =
  case runElab initEState (reifyRaw tm) (initElaborator (sMN 0 "hole") internalNS initContext emptyContext 0 Erased) of
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

reifyPlicity :: Term -> ElabD RPlicity
reifyPlicity (P (DCon _ _ _) n _)
  | n == tacN "Explicit" = return RExplicit
  | n == tacN "Implicit" = return RImplicit
  | n == tacN "Constraint" = return RConstraint
reifyPlicity tm = fail $ "Couldn't reify " ++ show tm ++ " as RPlicity."

reifyRFunArg :: Term -> ElabD RFunArg
reifyRFunArg (App _ (App _ (App _ (App _ (P (DCon _ _ _) n _) argN) argTy) argPl) argE)
  | n == tacN "MkFunArg" = liftM4 RFunArg
                             (reifyTTName argN)
                             (reifyRaw argTy)
                             (reifyPlicity argPl)
                             (reifyErasure argE)
reifyRFunArg aTm = fail $ "Couldn't reify " ++ show aTm ++ " as an RArg."

reifyTyDecl :: Term -> ElabD RTyDecl
reifyTyDecl (App _ (App _ (App _ (P (DCon _ _ _) n _) tyN) args) ret)
  | n == tacN "Declare" =
  do tyN'  <- reifyTTName tyN
     args' <- case unList args of
                Nothing -> fail $ "Couldn't reify " ++ show args ++ " as an arglist."
                Just xs -> mapM reifyRFunArg xs
     ret'  <- reifyRaw ret
     return $ RDeclare tyN' args' ret'
reifyTyDecl tm = fail $ "Couldn't reify " ++ show tm ++ " as a type declaration."

reifyFunDefn :: Term -> ElabD (RFunDefn Raw)
reifyFunDefn (App _ (App _ (App _ (P _ n _) (P _ t _)) fnN) clauses)
  | n == tacN "DefineFun" && t == reflm "Raw" =
  do fnN' <- reifyTTName fnN
     clauses' <- case unList clauses of
                   Nothing -> fail $ "Couldn't reify " ++ show clauses ++ " as a clause list"
                   Just cs -> mapM reifyC cs
     return $ RDefineFun fnN' clauses'
  where reifyC :: Term -> ElabD (RFunClause Raw)
        reifyC (App _ (App _ (App _ (P (DCon _ _ _) n _) (P _ t _)) lhs) rhs)
          | n == tacN "MkFunClause" && t == reflm "Raw" = liftM2 RMkFunClause
                                             (reifyRaw lhs)
                                             (reifyRaw rhs)
        reifyC (App _ (App _ (P (DCon _ _ _) n _) (P _ t _)) lhs)
          | n == tacN "MkImpossibleClause" && t == reflm "Raw" = fmap RMkImpossibleClause $ reifyRaw lhs
        reifyC tm = fail $ "Couldn't reify " ++ show tm ++ " as a clause."
reifyFunDefn tm = fail $ "Couldn't reify " ++ show tm ++ " as a function declaration."

reifyRConstructorDefn :: Term -> ElabD RConstructorDefn
reifyRConstructorDefn (App _ (App _ (App _ (P _ n _) cn) args) retTy)
  | n == tacN "Constructor", Just args' <- unList args
  = RConstructor <$> reifyTTName cn <*> mapM reifyRFunArg args' <*> reifyRaw retTy
reifyRConstructorDefn aTm = fail $ "Couldn't reify " ++ show aTm ++ " as an RConstructorDefn"

reifyRDataDefn :: Term -> ElabD RDataDefn
reifyRDataDefn (App _ (App _ (P _ n _) tyn) ctors)
  | n == tacN "DefineDatatype", Just ctors' <- unList ctors
  = RDefineDatatype <$> reifyTTName tyn <*> mapM reifyRConstructorDefn ctors'
reifyRDataDefn aTm = fail $ "Couldn't reify " ++ show aTm ++ " as an RDataDefn"

envTupleType :: Raw
envTupleType
  = raw_apply (Var pairTy) [ (Var $ reflm "TTName")
                           , (RApp (Var $ reflm "Binder") (Var $ reflm "TT"))
                           ]

reflectList :: Raw -> [Raw] -> Raw
reflectList ty []     = RApp (Var (sNS (sUN "Nil") ["List", "Prelude"])) ty
reflectList ty (x:xs) = RApp (RApp (RApp (Var (sNS (sUN "::") ["List", "Prelude"])) ty)
                                   x)
                             (reflectList ty xs)

-- | Apply Idris's implicit info to get a signature. The [PArg] should
-- come from a lookup in idris_implicits on IState.
getArgs :: [PArg] -> Raw -> ([RFunArg], Raw)
getArgs []     r = ([], r)
getArgs (a:as) (RBind n (Pi _ _ ty _) sc) =
  let (args, res) = getArgs as sc
      erased = if InaccessibleArg `elem` argopts a then RErased else RNotErased
      arg' = case a of
               PImp {} -> RFunArg n ty RImplicit erased
               PExp {} -> RFunArg n ty RExplicit erased
               PConstraint {} -> RFunArg n ty RConstraint erased
               PTacImplicit {} -> RFunArg n ty RImplicit erased
  in (arg':args, res)
getArgs _ r = ([], r)

unApplyRaw :: Raw -> (Raw, [Raw])
unApplyRaw tm = ua [] tm
  where
    ua args (RApp f a) = ua (a:args) f
    ua args t         = (t, args)

-- | Build the reflected function definition(s) that correspond(s) to
-- a provided unqualifed name
buildFunDefns :: IState -> Name -> [RFunDefn Term]
buildFunDefns ist n =
  [ mkFunDefn name clauses
  | (name, (clauses, _)) <- lookupCtxtName n $ idris_patdefs ist
  ]

  where mkFunDefn name clauses = RDefineFun name (map mkFunClause clauses)

        mkFunClause ([], lhs, Impossible) = RMkImpossibleClause lhs
        mkFunClause ([], lhs, rhs) = RMkFunClause lhs rhs
        mkFunClause (((n, ty) : ns), lhs, rhs) = mkFunClause (ns, bind lhs, bind rhs) where
          bind Impossible = Impossible
          bind tm = Bind n (PVar RigW ty) tm

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

        ctorSig params cn = do cty <- fmap forget (lookupTyExact cn ctxt)
                               argInfo <- lookupCtxtExact cn impls
                               let (args, res) = getArgs argInfo cty
                               return (cn, ctorArgsStatus args res params, res)

        argPos n [] res = findPos n res
          where findPos n app = case unApplyRaw app of
                                  (_, argL) -> findIndex (== Var n) argL
        argPos n (arg:args) res = if n == argName arg
                                     then Nothing
                                     else argPos n args res

        ctorArgsStatus :: [RFunArg] -> Raw -> [Int] -> [RCtorArg]
        ctorArgsStatus [] _ _ = []
        ctorArgsStatus (arg:args) res params =
          case argPos (argName arg) args res of
            Nothing -> RCtorField arg : ctorArgsStatus args res params
            Just i -> if i `elem` params
                         then RCtorParameter arg : ctorArgsStatus args res params
                         else RCtorField arg : ctorArgsStatus args res params

        mkDataType name (TI {param_pos = params, con_names = constrs}) =
          do (TyDecl (TCon _ _) ty) <- lookupDefExact name ctxt
             implInfo <- lookupCtxtExact name impls
             let (tcargs, tcres) = getTCArgs params implInfo (forget ty)
             ctors <- mapM (ctorSig params) constrs
             return $ RDatatype name tcargs tcres ctors

        getTCArgs :: [Int] -> [PArg] -> Raw -> ([RTyConArg], Raw)
        getTCArgs params implInfo tcTy =
          let (args, res) = getArgs implInfo tcTy
          in (tcArg args 0, res)
            where tcArg [] _ = []
                  tcArg (arg:args) i | i `elem` params = RParameter arg : tcArg args (i+1)
                                     | otherwise       = RIndex arg : tcArg args (i+1)


reflectErasure :: RErasure -> Raw
reflectErasure RErased    = Var (tacN "Erased")
reflectErasure RNotErased = Var (tacN "NotErased")

reflectPlicity :: RPlicity -> Raw
reflectPlicity RExplicit = Var (tacN "Explicit")
reflectPlicity RImplicit = Var (tacN "Implicit")
reflectPlicity RConstraint = Var (tacN "Constraint")

reflectArg :: RFunArg -> Raw
reflectArg (RFunArg n ty plic erasure) =
  RApp (RApp (RApp (RApp (Var $ tacN "MkFunArg") (reflectName n))
                   (reflectRaw ty))
              (reflectPlicity plic))
       (reflectErasure erasure)

reflectCtorArg :: RCtorArg -> Raw
reflectCtorArg (RCtorParameter arg) = RApp (Var $ tacN "CtorParameter") (reflectArg arg)
reflectCtorArg (RCtorField arg) = RApp (Var $ tacN "CtorField") (reflectArg arg)

reflectDatatype :: RDatatype -> Raw
reflectDatatype (RDatatype tyn tyConArgs tyConRes constrs) =
  raw_apply (Var $ tacN "MkDatatype") [ reflectName tyn
                                      , rawList (Var $ tacN "TyConArg") (map reflectConArg tyConArgs)
                                      , reflectRaw tyConRes
                                      , rawList (rawTripleTy (Var $ reflm "TTName")
                                                             (RApp (Var (sNS (sUN "List") ["List", "Prelude"]))
                                                                   (Var $ tacN "CtorArg"))
                                                             (Var $ reflm "Raw"))
                                                [ rawTriple ((Var $ reflm "TTName")
                                                            ,(RApp (Var (sNS (sUN "List") ["List", "Prelude"]))
                                                                   (Var $ tacN "CtorArg"))
                                                            ,(Var $ reflm "Raw"))
                                                            (reflectName cn
                                                            ,rawList (Var $ tacN "CtorArg")
                                                                     (map reflectCtorArg cargs)
                                                            ,reflectRaw cty)
                                                | (cn, cargs, cty) <- constrs
                                                ]
                                      ]
  where reflectConArg (RParameter a) =
          RApp (Var $ tacN "TyConParameter") (reflectArg a)
        reflectConArg (RIndex a) =
          RApp (Var $ tacN "TyConIndex") (reflectArg a)

reflectFunClause :: RFunClause Term -> Raw
reflectFunClause (RMkFunClause lhs rhs)    = raw_apply (Var $ tacN "MkFunClause")
                                                     $ (Var $ reflm "TT") : map reflect [ lhs, rhs ]

reflectFunClause (RMkImpossibleClause lhs) = raw_apply (Var $ tacN "MkImpossibleClause")
                                                       [ Var $ reflm "TT", reflect lhs ]

reflectFunDefn :: RFunDefn Term -> Raw
reflectFunDefn (RDefineFun name clauses) = raw_apply (Var $ tacN "DefineFun")
                                                     [ Var $ reflm "TT"
                                                     , reflectName name
                                                     , rawList (RApp (Var $ tacN "FunClause")
                                                                     (Var $ reflm "TT"))
                                                               (map reflectFunClause clauses)
                                                     ]

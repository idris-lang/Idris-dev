{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Idris.Core.DeepSeq where

import Idris.Core.TT
import Idris.Core.CaseTree
import Idris.Core.Evaluate

import Control.DeepSeq

instance NFData Name where
        rnf (UN x1) = rnf x1 `seq` ()
        rnf (NS x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (MN x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf NErased = ()
        rnf (SN x1) = rnf x1 `seq` ()
        rnf (SymRef x1) = rnf x1 `seq` ()

instance NFData SpecialName where
        rnf (WhereN x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (WithN x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (InstanceN x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (ParentN x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (MethodN x1) = rnf x1 `seq` ()
        rnf (CaseN x1) = rnf x1 `seq` ()
        rnf (ElimN x1) = rnf x1 `seq` ()
        rnf (InstanceCtorN x1) = rnf x1 `seq` ()
        rnf (MetaN x1 x2) = rnf x1 `seq` rnf x2 `seq` ()

instance NFData Universe where
        rnf NullType = ()
        rnf UniqueType = ()
        rnf AllTypes = ()

instance NFData Raw where
        rnf (Var x1) = rnf x1 `seq` ()
        rnf (RBind x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (RApp x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf RType = ()
        rnf (RUType x1) = rnf x1 `seq` ()
        rnf (RForce x1) = rnf x1 `seq` ()
        rnf (RConstant x1) = x1 `seq` ()

instance NFData FC where
        rnf (FC x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf NoFC = ()
        rnf (FileFC f) = rnf f `seq` ()

instance NFData Provenance where
        rnf ExpectedType = ()
        rnf InferredVal = ()
        rnf GivenVal = ()
        rnf (SourceTerm x1) = rnf x1 `seq` ()
        rnf (TooManyArgs x1) = rnf x1 `seq` ()

instance NFData UConstraint where
  rnf (ULT x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
  rnf (ULE x1 x2) = rnf x1 `seq` rnf x2 `seq` ()

instance NFData ConstraintFC where
  rnf (ConstraintFC x1 x2) = rnf x1 `seq` rnf x2 `seq` ()

instance NFData Err where
        rnf (Msg x1) = rnf x1 `seq` ()
        rnf (InternalMsg x1) = rnf x1 `seq` ()
        rnf (CantUnify x1 x2 x3 x4 x5 x6)
          = rnf x1 `seq`
              rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` ()
        rnf (InfiniteUnify x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (CantConvert x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (UnifyScope x1 x2 x3 x4)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (ElaboratingArg x1 x2 x3 x4)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (CantInferType x1) = rnf x1 `seq` ()
        rnf (CantMatch x1) = rnf x1 `seq` ()
        rnf (ReflectionError x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (ReflectionFailed x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (CantSolveGoal x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (UniqueError x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (UniqueKindError x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (NotEquality x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (NonFunctionType x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (CantIntroduce x1) = rnf x1 `seq` ()
        rnf (TooManyArguments x1) = rnf x1 `seq` ()
        rnf (WithFnType x1) = rnf x1 `seq` ()
        rnf (NoSuchVariable x1) = rnf x1 `seq` ()
        rnf (NoTypeDecl x1) = rnf x1 `seq` ()
        rnf (NotInjective x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (CantResolve x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (InvalidTCArg x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (CantResolveAlts x1) = rnf x1 `seq` ()
        rnf (NoValidAlts x1) = rnf x1 `seq` ()
        rnf (IncompleteTerm x1) = rnf x1 `seq` ()
        rnf (NoEliminator x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (UniverseError x1 x2 x3 x4 x5) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()
        rnf ProgramLineComment = ()
        rnf (Inaccessible x1) = rnf x1 `seq` ()
        rnf (UnknownImplicit x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (NonCollapsiblePostulate x1) = rnf x1 `seq` ()
        rnf (AlreadyDefined x1) = rnf x1 `seq` ()
        rnf (ProofSearchFail x1) = rnf x1 `seq` ()
        rnf (NoRewriting x1) = rnf x1 `seq` ()
        rnf (At x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (Elaborating x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (ProviderError x1) = rnf x1 `seq` ()
        rnf (LoadingFailed x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (ElabScriptDebug x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (ElabScriptStuck x1) = rnf x1 `seq` ()
        rnf (RunningElabScript x1) = rnf x1 `seq` ()

instance NFData ErrorReportPart where
  rnf (TextPart x1) = rnf x1 `seq` ()
  rnf (TermPart x1) = rnf x1 `seq` ()
  rnf (RawPart x1) = rnf x1 `seq` ()
  rnf (NamePart x1) = rnf x1 `seq` ()
  rnf (SubReport x1) = rnf x1 `seq` ()

instance NFData ImplicitInfo where
        rnf (Impl x1) = rnf x1 `seq` ()

instance (NFData b) => NFData (Binder b) where
        rnf (Lam x1) = rnf x1 `seq` ()
        rnf (Pi x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (Let x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (NLet x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (Hole x1) = rnf x1 `seq` ()
        rnf (GHole x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (Guess x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PVar x1) = rnf x1 `seq` ()
        rnf (PVTy x1) = rnf x1 `seq` ()

instance NFData UExp where
        rnf (UVar x1) = rnf x1 `seq` ()
        rnf (UVal x1) = rnf x1 `seq` ()

instance NFData NameType where
        rnf Bound = ()
        rnf Ref = ()
        rnf (DCon x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (TCon x1 x2) = rnf x1 `seq` rnf x2 `seq` ()

instance NFData NativeTy where
        rnf IT8 = ()
        rnf IT16 = ()
        rnf IT32 = ()
        rnf IT64 = ()

instance NFData IntTy where
        rnf (ITFixed x1) = rnf x1 `seq` ()
        rnf ITNative = ()
        rnf ITBig = ()
        rnf ITChar = ()

instance NFData ArithTy where
        rnf (ATInt x1) = rnf x1 `seq` ()
        rnf ATFloat = ()

instance NFData Const where
        rnf (I x1) = rnf x1 `seq` ()
        rnf (BI x1) = rnf x1 `seq` ()
        rnf (Fl x1) = rnf x1 `seq` ()
        rnf (Ch x1) = rnf x1 `seq` ()
        rnf (Str x1) = rnf x1 `seq` ()
        rnf (B8 x1) = rnf x1 `seq` ()
        rnf (B16 x1) = rnf x1 `seq` ()
        rnf (B32 x1) = rnf x1 `seq` ()
        rnf (B64 x1) = rnf x1 `seq` ()
        rnf (AType x1) = rnf x1 `seq` ()
        rnf WorldType = ()
        rnf TheWorld = ()
        rnf StrType = ()
        rnf VoidType = ()
        rnf Forgot = ()

instance (NFData n) => NFData (TT n) where
        rnf (P x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (V x1) = rnf x1 `seq` ()
        rnf (Bind x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (App x1 x2 x3) = rnf x2 `seq` rnf x3 `seq` ()
        rnf (Constant x1) = rnf x1 `seq` ()
        rnf (Proj x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf Erased = ()
        rnf Impossible = ()
        rnf (TType x1) = rnf x1 `seq` ()
        rnf (UType _) = ()

instance NFData Accessibility where
        rnf Public = ()
        rnf Frozen = ()
        rnf Hidden = ()

 
instance NFData Totality where
        rnf (Total x1) = rnf x1 `seq` ()
        rnf Productive = ()
        rnf (Partial x1) = rnf x1 `seq` ()
        rnf Unchecked = ()
        rnf Generated = ()
        
instance NFData PReason where
        rnf (Other x1) = rnf x1 `seq` ()
        rnf Itself = ()
        rnf NotCovering = ()
        rnf NotPositive = ()
        rnf (UseUndef x1) = rnf x1 `seq` ()
        rnf ExternalIO = ()
        rnf BelieveMe = ()
        rnf (Mutual x1) = rnf x1 `seq` ()
        rnf NotProductive = ()

instance NFData MetaInformation where
        rnf EmptyMI = ()
        rnf (DataMI x1) = rnf x1 `seq` ()

instance NFData Def where
        rnf (Function x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (TyDecl x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (Operator x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (CaseOp x1 x2 x3 x4 x5 x6)
          = rnf x1 `seq`
              rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` ()

instance NFData CaseInfo where
        rnf (CaseInfo x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
 
instance NFData CaseDefs where
        rnf (CaseDefs x1 x2 x3 x4)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()

instance (NFData t) => NFData (SC' t) where
        rnf (Case _ x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (ProjCase x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (STerm x1) = rnf x1 `seq` ()
        rnf (UnmatchedCase x1) = rnf x1 `seq` ()
        rnf ImpossibleCase = ()

instance (NFData t) => NFData (CaseAlt' t) where
        rnf (ConCase x1 x2 x3 x4)
          = x1 `seq` x2 `seq` x3 `seq` rnf x4 `seq` ()
        rnf (FnCase x1 x2 x3) = x1 `seq` x2 `seq` rnf x3 `seq` ()
        rnf (ConstCase x1 x2) = x1 `seq` rnf x2 `seq` ()
        rnf (SucCase x1 x2) = x1 `seq` rnf x2 `seq` ()
        rnf (DefaultCase x1) = rnf x1 `seq` ()

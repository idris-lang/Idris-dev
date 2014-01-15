module Idris.Core.DeepSeq where

import Idris.Core.TT

import Control.DeepSeq

instance NFData Name where
        rnf (UN x1) = rnf x1 `seq` ()
        rnf (NS x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (MN x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf NErased = ()
        rnf (SN x1) = rnf x1 `seq` ()

instance NFData SpecialName where
        rnf (WhereN x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (InstanceN x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (ParentN x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (MethodN x1) = rnf x1 `seq` ()
        rnf (CaseN x1) = rnf x1 `seq` ()
        rnf (ElimN x1) = rnf x1 `seq` ()

instance NFData Raw where
        rnf (Var x1) = rnf x1 `seq` ()
        rnf (RBind x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (RApp x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf RType = ()
        rnf (RForce x1) = rnf x1 `seq` ()
        rnf (RConstant x1) = x1 `seq` ()

instance NFData FC where
        rnf (FC x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()

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
        rnf (CantInferType x1) = rnf x1 `seq` ()
        rnf (NonFunctionType x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (CantIntroduce x1) = rnf x1 `seq` ()
        rnf (NoSuchVariable x1) = rnf x1 `seq` ()
        rnf (NoTypeDecl x1) = rnf x1 `seq` ()
        rnf (NotInjective x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (CantResolve x1) = rnf x1 `seq` ()
        rnf (CantResolveAlts x1) = rnf x1 `seq` ()
        rnf (IncompleteTerm x1) = rnf x1 `seq` ()
        rnf UniverseError = ()
        rnf ProgramLineComment = ()
        rnf (Inaccessible x1) = rnf x1 `seq` ()
        rnf (NonCollapsiblePostulate x1) = rnf x1 `seq` ()
        rnf (AlreadyDefined x1) = rnf x1 `seq` ()
        rnf (ProofSearchFail x1) = rnf x1 `seq` ()
        rnf (NoRewriting x1) = rnf x1 `seq` ()
        rnf (At x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (Elaborating x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (ProviderError x1) = rnf x1 `seq` ()
        rnf (LoadingFailed x1 x2) = rnf x1 `seq` rnf x2 `seq` ()

instance (NFData b) => NFData (Binder b) where
        rnf (Lam x1) = rnf x1 `seq` ()
        rnf (Pi x1) = rnf x1 `seq` ()
        rnf (Let x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (NLet x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (Hole x1) = rnf x1 `seq` ()
        rnf (GHole x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (Guess x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PVar x1) = rnf x1 `seq` ()
        rnf (PVTy x1) = rnf x1 `seq` ()

instance NFData UExp where
        rnf (UVar x1) = rnf x1 `seq` ()
        rnf (UVal x1) = rnf x1 `seq` ()

instance NFData NameType where
        rnf Bound = ()
        rnf Ref = ()
        rnf (DCon x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (TCon x1 x2) = rnf x1 `seq` rnf x2 `seq` ()

instance (NFData n) => NFData (TT n) where
        rnf (P x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (V x1) = rnf x1 `seq` ()
        rnf (Bind x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (App x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (Constant x1) = x1 `seq` ()
        rnf (Proj x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf Erased = ()
        rnf Impossible = ()
        rnf (TType x1) = rnf x1 `seq` ()


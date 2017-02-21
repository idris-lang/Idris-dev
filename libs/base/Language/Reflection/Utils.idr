module Language.Reflection.Utils

import Language.Reflection
import Language.Reflection.Elab
import Language.Reflection.Errors

%access public export

--------------------------------------------------------
-- Tactic construction conveniences
--------------------------------------------------------

total
seq : List Tactic -> Tactic
seq []      = GoalType "This is an impossible case" Trivial
seq [t]     = t
seq (t::ts) = t `Seq` seq ts

total
try : List Tactic -> Tactic
try []      = GoalType "This is an impossible case" Trivial
try [t]     = t
try (t::ts) = t `Try` seq ts


--------------------------------------------------------
-- For use in tactic scripts
--------------------------------------------------------
total
mkPair : a -> b -> (a, b)
mkPair a b = (a, b)


--------------------------------------------------------
-- Tools for constructing proof terms directly
--------------------------------------------------------
total
getUName : TTName -> Maybe String
getUName (UN n)    = Just n
getUName (NS n ns) = getUName n
getUName _         = Nothing

namespace TT
  total
  unApply : TT -> (TT, List TT)
  unApply t = unA t []
    where unA : TT -> List TT -> (TT, List TT)
          unA (App fn arg) args = unA fn (arg::args)
          unA tm           args = (tm, args)

  total
  mkApp : Foldable f => TT -> f TT -> TT
  mkApp f args = foldl App f args

namespace Raw
  total
  unApply : Raw -> (Raw, List Raw)
  unApply tm = unApply' tm []
    where unApply' : Raw -> List Raw -> (Raw, List Raw)
          unApply' (RApp f x) xs = unApply' f (x::xs)
          unApply' notApp xs = (notApp, xs)

  total
  mkApp : Foldable f => Raw -> f Raw -> Raw
  mkApp f args = foldl RApp f args


total
binderTy : Binder t -> t
binderTy (Lam t)       = t
binderTy (Pi t _)      = t
binderTy (Let t1 t2)   = t1
binderTy (Hole t)      = t
binderTy (GHole t)     = t
binderTy (Guess t1 t2) = t1
binderTy (PVar t)      = t
binderTy (PVTy t)      = t

implementation Show SourceLocation where
  showPrec d (FileLoc filename line col) = showCon d "FileLoc" $ showArg filename ++ showArg line ++ showArg col

implementation Eq SourceLocation where
  (FileLoc fn s e) == (FileLoc fn' s' e') = fn == fn' && s == s' && e == e'

mutual
  implementation Show SpecialName where
    showPrec d (WhereN i n1 n2) = showCon d "WhereN" $ showArg i ++
                            showArg n1 ++ showArg n2
    showPrec d (WithN i n) = showCon d "WithN" $ showArg i ++ showArg n
    showPrec d (ImplementationN i ss) = showCon d "ImplementationN" $ showArg i ++ showArg ss
    showPrec d (ParentN n s) = showCon d "ParentN" $ showArg n ++ showArg s
    showPrec d (MethodN n) = showCon d "MethodN" $ showArg n
    showPrec d (CaseN fc n) = showCon d "CaseN" $ showArg fc ++ showArg n
    showPrec d (ElimN n) = showCon d "ElimN" $ showArg n
    showPrec d (ImplementationCtorN n) = showCon d "ImplementationCtorN" $ showArg n
    showPrec d (MetaN parent meta) = showCon d "MetaN" $ showArg parent ++ showArg meta

  implementation Show TTName where
    showPrec d (UN str)   = showCon d "UN" $ showArg str
    showPrec d (NS n ns)  = showCon d "NS" $ showArg n ++ showArg ns
    showPrec d (MN i str) = showCon d "MN" $ showArg i ++ showArg str
    showPrec d (SN sn)    = showCon d "SN" $ assert_total (showArg sn)

mutual
  implementation Eq TTName where
    (UN str1)  == (UN str2)     = str1 == str2
    (NS n ns)  == (NS n' ns')   = n == n' && ns == ns'
    (MN i str) == (MN i' str')  = i == i' && str == str'
    (SN sn)    == (SN sn')      = assert_total $ sn == sn'
    x          == y             = False

  implementation Eq SpecialName where
    (WhereN i n1 n2)        == (WhereN i' n1' n2')      = i == i' && n1 == n1' && n2 == n2'
    (WithN i n)             == (WithN i' n')            = i == i' && n == n'
    (ImplementationN i ss)  == (ImplementationN i' ss') = i == i' && ss == ss'
    (ParentN n s)           == (ParentN n' s')          = n == n' && s == s'
    (MethodN n)             == (MethodN n')             = n == n'
    (CaseN fc n)            == (CaseN fc' n')           = fc == fc' && n == n'
    (ElimN n)               == (ElimN n')               = n == n'
    (ImplementationCtorN n) == (ImplementationCtorN n') = n == n'
    (MetaN parent meta)     == (MetaN parent' meta')    = parent == parent' && meta == meta'
    _                       == _                        = False

implementation Show TTUExp where
  showPrec d (UVar ns i) = showCon d "UVar" $ showArg ns ++ showArg i
  showPrec d (UVal i) = showCon d "UVal" $ showArg i

implementation Eq TTUExp where
  (UVar nsi i) == (UVar nsj j) = nsi == nsj && i == j
  (UVal i)     == (UVal j)     = i == j
  x            == y            = False

implementation Show NativeTy where
  show IT8  = "IT8"
  show IT16 = "IT16"
  show IT32 = "IT32"
  show IT64 = "IT64"

implementation Show IntTy where
  showPrec d (ITFixed t) = showCon d "ITFixed" $ showArg t
  showPrec d ITNative    = "ITNative"
  showPrec d ITBig       = "ITBig"
  showPrec d ITChar      = "ITChar"

implementation Show ArithTy where
  showPrec d (ATInt t) = showCon d "ATInt" $ showArg t
  showPrec d ATDouble   = "ATDouble"

implementation Show Const where
  showPrec d (I i)      = showCon d "I" $ showArg i
  showPrec d (BI n)     = showCon d "BI" $ showArg n
  showPrec d (Fl f)     = showCon d "Fl" $ showArg f
  showPrec d (Ch c)     = showCon d "Ch" $ showArg c
  showPrec d (Str str)  = showCon d "Str" $ showArg str
  showPrec d (B8 b)     = showCon d "B8" $ showArg b
  showPrec d (B16 b)    = showCon d "B16" $ showArg b
  showPrec d (B32 b)    = showCon d "B32" $ showArg b
  showPrec d (B64 b)    = showCon d "B64" $ showArg b
  showPrec d (AType x)  = showCon d "AType" $ showArg x
  showPrec d StrType    = "StrType"
  showPrec d VoidType   = "VoidType"
  showPrec d Forgot     = "Forgot"
  showPrec d WorldType  = "WorldType"
  showPrec d TheWorld   = "TheWorld"

implementation Eq NativeTy where
  IT8  == IT8  = True
  IT16 == IT16 = True
  IT32 == IT32 = True
  IT64 == IT64 = True
  _    == _    = False

implementation Eq Reflection.IntTy where
  (ITFixed x) == (ITFixed y) = x == y
  ITNative    == ITNative    = True
  ITBig       == ITBig       = True
  ITChar      == ITChar      = True
  _           == _           = False

implementation Eq ArithTy where
  (ATInt x) == (ATInt y) = x == y
  ATDouble  == ATDouble   = True
  _         == _         = False

implementation Eq Const where
  (I x)          == (I y)           = x == y
  (BI x)         == (BI y)          = x == y
  (Fl x)         == (Fl y)          = x == y
  (Ch x)         == (Ch y)          = x == y
  (Str x)        == (Str y)         = x == y
  (B8 x)         == (B8 y)          = x == y
  (B16 x)        == (B16 y)         = x == y
  (B32 x)        == (B32 y)         = x == y
  (B64 x)        == (B64 y)         = x == y
  (AType x)      == (AType y)       = x == y
  StrType        == StrType         = True
  VoidType       == VoidType        = True
  Forgot         == Forgot          = True
  _              == _               = False


implementation Show NameType where
  showPrec d Bound = "Bound"
  showPrec d Ref = "Ref"
  showPrec d (DCon t ar) = showCon d "DCon" $ showArg t ++ showArg ar
  showPrec d (TCon t ar) = showCon d "TCon" $ showArg t ++ showArg ar

implementation Eq NameType where
  Bound       == Bound          = True
  Ref         == Ref            = True
  (DCon t ar) == (DCon t' ar')  = t == t' && ar == ar'
  (TCon t ar) == (TCon t' ar')  = t == t' && ar == ar'
  x           == y              = False

implementation (Show a) => Show (Binder a) where
  showPrec d (Lam t) = showCon d "Lam" $ showArg t
  showPrec d (Pi t1 t2) = showCon d "Pi" $ showArg t1 ++ showArg t2
  showPrec d (Let t1 t2) = showCon d "Let" $ showArg t1 ++ showArg t2
  showPrec d (Hole t) = showCon d "Hole" $ showArg t
  showPrec d (GHole t) = showCon d "GHole" $ showArg t
  showPrec d (Guess t1 t2) = showCon d "Guess" $ showArg t1 ++ showArg t2
  showPrec d (PVar t) = showCon d "PVar" $ showArg t
  showPrec d (PVTy t) = showCon d "PVTy" $ showArg t

implementation (Eq a) => Eq (Binder a) where
  (Lam t)       == (Lam t')         = t == t'
  (Pi t k)      == (Pi t' k')       = t == t' && k == k'
  (Let t1 t2)   == (Let t1' t2')    = t1 == t1' && t2 == t2'
  (Hole t)      == (Hole t')        = t == t'
  (GHole t)     == (GHole t')       = t == t'
  (Guess t1 t2) == (Guess t1' t2')  = t1 == t1' && t2 == t2'
  (PVar t)      == (PVar t')        = t == t'
  (PVTy t)      == (PVTy t')        = t == t'
  x             == y                = False

implementation Show TT where
  showPrec = my_show
    where my_show : Prec -> TT -> String
          my_show d (P nt n t) = assert_total $ showCon d "P" $ showArg nt ++ showArg n ++ showArg t
          my_show d (V i) = assert_total $ showCon d "V" $ showArg i
          my_show d (Bind n b t) = assert_total $ showCon d "Bind" $ showArg n ++ showArg b ++ showArg t
          my_show d (App t1 t2) = assert_total $ showCon d "App" $ showArg t1 ++ showArg t2
          my_show d (TConst c) = assert_total $ showCon d "TConst" $ showArg c
          my_show d Erased = "Erased"
          my_show d (TType u) = assert_total $ showCon d "TType" $ showArg u
          my_show d (UType u) = "UType"

implementation Eq Universe where
  Reflection.NullType   == Reflection.NullType   = True
  Reflection.UniqueType == Reflection.UniqueType = True
  Reflection.AllTypes   == Reflection.AllTypes   = True
  _                     == _                     = False

implementation Eq TT where
  a == b = equalp a b
    where equalp : TT -> TT -> Bool
          equalp (P nt n t)   (P nt' n' t')    = assert_total $ nt == nt' && n == n' && t == t'
          equalp (V i)        (V i')           = assert_total $ i == i'
          equalp (Bind n b t) (Bind n' b' t')  = assert_total $ n == n' && b == b' && t == t'
          equalp (App t1 t2)  (App t1' t2')    = assert_total $ t1 == t1' && t2 == t2'
          equalp (TConst c)   (TConst c')      = c == c'
          equalp Erased       Erased           = True
          equalp (TType u)    (TType u')       = u == u'
          equalp (UType u)    (UType u')       = u == u'
          equalp x            y                = False

implementation Eq Raw where
  a == b = equalp a b
    where equalp : Raw -> Raw -> Bool
          equalp (Var x)         (Var y)         = assert_total $ x == y
          equalp (RBind x b1 e1) (RBind y b2 e2) = assert_total $ x == y && b1 == b2 && e1 == e2
          equalp (RApp f1 a1)    (RApp f2 a2)    = assert_total $ f1 == f2 && a1 == a2
          equalp RType           RType           = True
          equalp (RUType u1)     (RUType u2)     = u1 == u2
          equalp (RConstant c1)  (RConstant c2)  = c1 == c2
          equalp _               _               = False


total
forget : TT -> Maybe Raw
forget tm = fe [] tm
  where
    atIndex : List a -> Int -> Maybe a
    atIndex [] _ = Nothing
    atIndex (x::xs) n =
      case compare n 0 of
        EQ => Just x
        LT => Nothing
        GT => atIndex xs (n-1)

    fe : List TTName -> TT -> Maybe Raw
    fe env (P _ n _)     = Just $ Var n
    fe env (V i)         = [| Var (atIndex env i) |]
    fe env (Bind n b sc) = [| RBind (pure n)
                                    (assert_total $ traverse (fe env) b)
                                    (fe (n::env) sc) |]
    fe env (App f a)     = [| RApp (fe env f) (fe env a) |]
    fe env (TConst c)    = Just $ RConstant c
    fe env (TType i)     = Just RType
    fe env (UType uni)   = Just (RUType uni)
    fe env Erased        = Just $ RConstant Forgot

implementation Show Raw where
  showPrec = my_show
    where my_show : Prec -> Raw -> String
          my_show d (Var n) = assert_total $ showCon d "Var" $ showArg n
          my_show d (RBind n b tm) = assert_total $ showCon d "RBind" $ showArg n ++ showArg b ++ " " ++ my_show App tm
          my_show d (RApp tm tm') = assert_total $ showCon d "RApp" $ " " ++ my_show App tm ++ " " ++ my_show App tm'
          my_show d RType = "RType"
          my_show d (RConstant c) = assert_total $ showCon d "RConstant" $ showArg c
          my_show d (RUType u) = "RUType" 


implementation Show Err where
  showPrec d (Msg x) = showCon d "Msg" $ showArg x
  showPrec d (InternalMsg x) = showCon d "InternalMsg" $ showArg x
  showPrec d (CantUnify x tm tm' err xs y) = showCon d "CantUnify" $ showArg x ++
                                       showArg tm ++ showArg tm' ++ showArg err ++
                                       showArg xs ++ showArg y
  showPrec d (InfiniteUnify n tm xs) = showCon d "InfiniteUnify" $ showArg n ++ showArg tm ++ showArg xs
  showPrec d (CantConvert tm tm' xs) = showCon d "CantConvert" $ showArg tm ++ showArg tm' ++ showArg xs
  showPrec d (CantSolveGoal tm ctxt) = showCon d "CantSolveGoal" $ showArg tm ++ showArg ctxt
  showPrec d (UnifyScope n n' tm xs) = showCon d "UnifyScope" $ showArg n ++ showArg n' ++ showArg tm ++ showArg xs
  showPrec d (CantInferType x) = showCon d "CantInferType" $ showArg x
  showPrec d (NonFunctionType tm tm') = showCon d "NonFunctionType" $ showArg tm ++ showArg tm'
  showPrec d (NotEquality tm tm') = showCon d "NotEquality" $ showArg tm ++ showArg tm'
  showPrec d (TooManyArguments n) = showCon d "TooManyArguments" $ showArg n
  showPrec d (CantIntroduce tm) = showCon d "CantIntroduce" $ showArg tm
  showPrec d (NoSuchVariable n) = showCon d "NoSuchVariable" $ showArg n
  showPrec d (WithFnType tm) = showCon d "WithFnType" $ showArg tm
  showPrec d (CantMatch tm) = showCon d "CantMatch" $ showArg tm
  showPrec d (NoTypeDecl n) = showCon d "NoTypeDecl" $ showArg n
  showPrec d (NotInjective tm tm' x) = showCon d "NotInjective" $ showArg tm ++ showArg tm'
  showPrec d (CantResolve tm e) = showCon d "CantResolve" $ showArg tm ++ showArg e
  showPrec d (InvalidTCArg n tm) = showCon d "InvalidTCName" $ showArg n ++ showArg tm
  showPrec d (CantResolveAlts xs) = showCon d "CantResolveAlts" $ showArg xs
  showPrec d (NoValidAlts xs) = showCon d "NoValidAlts" $ showArg xs
  showPrec d (IncompleteTerm tm) = showCon d "IncompleteTerm" $ showArg tm
  showPrec d (NoEliminator s tm) = showCon d "NoEliminator" $ showArg s ++ showArg tm
  showPrec d UniverseError = "UniverseError"
  showPrec d ProgramLineComment = "ProgramLineComment"
  showPrec d (Inaccessible n) = showCon d "Inaccessible" $ showArg n
  showPrec d (UnknownImplicit n f) = showCon d "UnknownImplicit" $ showArg n ++ showArg f
  showPrec d (NonCollapsiblePostulate n) = showCon d "NonCollapsiblePostulate" $ showArg n
  showPrec d (AlreadyDefined n) = showCon d "AlreadyDefined" $ showArg n
  showPrec d (ProofSearchFail err) = showCon d "ProofSearchFail" $ showArg err
  showPrec d (NoRewriting ltm rtm typ) = showCon d "NoRewriting" $ showArg ltm ++ showArg rtm ++ showArg typ
  showPrec d (ProviderError x) = showCon d "ProviderError" $ showArg x
  showPrec d (LoadingFailed x err) = showCon d "LoadingFailed" $ showArg x ++ showArg err

-------------------------
-- Idiom brackets for Raw
-------------------------

(<*>) : Raw -> Raw -> Raw
(<*>) = RApp

pure : Raw -> Raw
pure = id

--------------------------------------
-- Implementations for definition reflection
--------------------------------------
implementation Show Erasure where
  show Erased    = "Erased"
  show NotErased = "NotErased"

implementation Show Plicity where
  show Explicit = "Explicit"
  show Implicit = "Implicit"
  show Constraint = "Constraint"

implementation Show FunArg where
  showPrec d (MkFunArg n ty plic era) = showCon d "MkFunArg" $ showArg n ++
                                        showArg ty ++ showArg plic ++ showArg era

implementation Show CtorArg where
  showPrec d (CtorParameter fa) = showCon d "CtorParameter" $ showArg fa
  showPrec d (CtorField fa) = showCon d "CtorField" $ showArg fa

implementation Show TyDecl where
  showPrec d (Declare fn args ret) = showCon d "Declare" $ showArg fn ++
                                     showArg args ++ showArg ret

implementation Show tm => Show (FunClause tm) where
  showPrec d (MkFunClause lhs rhs) =
      showCon d "MkFunClause" $ showArg lhs ++ showArg rhs
  showPrec d (MkImpossibleClause lhs) =
      showCon d "MkImpossibleClause" $ showArg lhs

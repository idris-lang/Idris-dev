module Language.Reflection.Utils

import Language.Reflection
import Language.Reflection.Errors

%default total

--------------------------------------------------------
-- Tactic construction conveniences
--------------------------------------------------------

seq : List Tactic -> Tactic
seq []      = GoalType "This is an impossible case" Trivial
seq [t]     = t
seq (t::ts) = t `Seq` seq ts

try : List Tactic -> Tactic
try []      = GoalType "This is an impossible case" Trivial
try [t]     = t
try (t::ts) = t `Try` seq ts


--------------------------------------------------------
-- For use in tactic scripts
--------------------------------------------------------
mkPair : a -> b -> (a, b)
mkPair a b = (a, b)


--------------------------------------------------------
-- Tools for constructing proof terms directly
--------------------------------------------------------

getUName : TTName -> Maybe String
getUName (UN n)    = Just n
getUName (NS n ns) = getUName n
getUName _         = Nothing

unApply : TT -> (TT, List TT)
unApply t = unA t []
  where unA : TT -> List TT -> (TT, List TT)
        unA (App fn arg) args = unA fn (arg::args)
        unA tm           args = (tm, args)

mkApp : TT -> List TT -> TT
mkApp tm []      = tm
mkApp tm (a::as) = mkApp (App tm a) as

binderTy : (Eq t) => Binder t -> t
binderTy (Lam t)       = t
binderTy (Pi t _)      = t
binderTy (Let t1 t2)   = t1
binderTy (NLet t1 t2)  = t1
binderTy (Hole t)      = t
binderTy (GHole t)     = t
binderTy (Guess t1 t2) = t1
binderTy (PVar t)      = t
binderTy (PVTy t)      = t

instance Show TTName where
  show (UN str)   = "(UN " ++ str ++ ")"
  show (NS n ns)  = "(NS " ++ show n ++ " " ++ show ns ++ ")"
  show (MN i str) = "(MN " ++ show i ++ " " ++ show str ++ ")"
  show NErased    = "NErased"

instance Eq TTName where
  (UN str1)  == (UN str2)     = str1 == str2
  (NS n ns)  == (NS n' ns')   = n == n' && ns == ns'
  (MN i str) == (MN i' str')  = i == i' && str == str'
  NErased    == NErased       = True
  x          == y             = False

instance Show TTUExp where
  show (UVar i) = "(UVar " ++ show i ++ ")"
  show (UVal i) = "(UVal " ++ show i ++ ")"

instance Eq TTUExp where
  (UVar i) == (UVar j) = i == j
  (UVal i) == (UVal j) = i == j
  x        == y        = False

instance Show Const where
  show (I i)      = "(I " ++ show i ++ ")"
  show (BI n)     = "(BI " ++ show n ++ ")"
  show (Fl f)     = "(Fl " ++ show f ++ ")"
  show (Ch c)     = "(Ch " ++ show c ++ ")"
  show (Str str)  = "(Str " ++ show str ++ ")"
  show (B8 b)     = "(B8 ...)"
  show (B16 b)    = "(B16 ...)"
  show (B32 b)    = "(B32 ...)"
  show (B64 b)    = "(B64 ...)"
  show (B8V xs)   = "(B8V ...)"
  show (B16V xs) = "(B16V ...)"
  show (B32V xs) = "(B32V ...)"
  show (B64V xs) = "(B64V ...)"
  show (AType x) = "(AType ...)"
  show StrType = "StrType"
  show PtrType = "PtrType"
  show ManagedPtrType = "ManagedPtrType"
  show BufferType = "BufferType"
  show VoidType = "VoidType"
  show Forgot = "Forgot"

instance Eq NativeTy where
  IT8  == IT8  = True
  IT16 == IT16 = True
  IT32 == IT32 = True
  IT64 == IT64 = True
  _    == _    = False

instance Eq Reflection.IntTy where
  (ITFixed x) == (ITFixed y) = x == y
  ITNative    == ITNative    = True
  ITBig       == ITBig       = True
  ITChar      == ITChar      = True
  (ITVec x i) == (ITVec y j) = x == y && i == j
  _           == _           = False

instance Eq ArithTy where
  (ATInt x) == (ATInt y) = x == y
  ATFloat   == ATFloat   = True
  _         == _         = False

instance Eq Const where
  (I x)          == (I y)           = x == y
  (BI x)         == (BI y)          = x == y
  (Fl x)         == (Fl y)          = x == y
  (Ch x)         == (Ch y)          = x == y
  (Str x)        == (Str y)         = x == y
  (B8 x)         == (B8 y)          = x == y
  (B16 x)        == (B16 y)         = x == y
  (B32 x)        == (B32 y)         = x == y
  (B64 x)        == (B64 y)         = x == y
  (B8V xs)       == (B8V ys)        = False -- TODO
  (B16V xs)      == (B16V ys)       = False -- TODO
  (B32V xs)      == (B32V ys)       = False -- TODO
  (B64V xs)      == (B64V ys)       = False -- TODO
  (AType x)      == (AType y)       = x == y
  StrType        == StrType         = True
  PtrType        == PtrType         = True
  ManagedPtrType == ManagedPtrType  = True
  BufferType     == BufferType      = True
  VoidType       == VoidType        = True
  Forgot         == Forgot          = True
  _              == _               = False


instance Show NameType where
  show Bound = "Bound"
  show Ref = "Ref"
  show (DCon t ar) = "(DCon " ++ show t ++ " " ++ show ar ++ ")"
  show (TCon t ar) = "(TCon " ++ show t ++ " " ++ show ar ++ ")"

instance Eq NameType where
  Bound       == Bound          = True
  Ref         == Ref            = True
  (DCon t ar) == (DCon t' ar')  = t == t' && ar == ar'
  (TCon t ar) == (TCon t' ar')  = t == t' && ar == ar'
  x           == y              = False

instance (Show a) => Show (Binder a) where
  show (Lam t) = "(Lam " ++ show t ++ ")"
  show (Pi t _) = "(Pi " ++ show t ++ ")"
  show (Let t1 t2) = "(Let " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (NLet t1 t2) = "(NLet " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Hole t) = "(Hole " ++ show t ++ ")"
  show (GHole t) = "(GHole " ++ show t ++ ")"
  show (Guess t1 t2) = "(Guess " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (PVar t) = "(PVar " ++ show t ++ ")"
  show (PVTy t) = "(PVTy " ++ show t ++ ")"

instance (Eq a) => Eq (Binder a) where
  (Lam t)       == (Lam t')         = t == t'
  (Pi t k)      == (Pi t' k')       = t == t' && k == k'
  (Let t1 t2)   == (Let t1' t2')    = t1 == t1' && t2 == t2'
  (NLet t1 t2)  == (NLet t1' t2')   = t1 == t1' && t2 == t2'
  (Hole t)      == (Hole t')        = t == t'
  (GHole t)     == (GHole t')       = t == t'
  (Guess t1 t2) == (Guess t1' t2')  = t1 == t1' && t2 == t2'
  (PVar t)      == (PVar t')        = t == t'
  (PVTy t)      == (PVTy t')        = t == t'
  x             == y                = False

instance Show TT where
  show = my_show
    where %assert_total my_show : TT -> String
          my_show (P nt n t) = "(P " ++ show nt ++ " " ++ show n ++ " " ++ show t ++ ")"
          my_show (V i) = "(V " ++ show i ++ ")"
          my_show (Bind n b t) = "(Bind " ++ show n ++ " " ++ show b ++ " " ++ show t ++ ")"
          my_show (App t1 t2) = "(App " ++ show t1 ++ " " ++ show t2 ++ ")"
          my_show (TConst c) = "(TConst " ++ show c ++ ")"
          my_show (Proj tm i) = "(Proj " ++ show tm ++ " " ++ show i ++ ")"
          my_show Erased = "Erased"
          my_show Impossible = "Impossible"
          my_show (TType u) = "(TType " ++ show u ++ ")"

instance Eq TT where
  a == b = equalp a b
    where %assert_total equalp : TT -> TT -> Bool
          equalp (P nt n t)   (P nt' n' t')    = nt == nt' && n == n' && t == t'
          equalp (V i)        (V i')           = i == i'
          equalp (Bind n b t) (Bind n' b' t')  = n == n' && b == b' && t == t'
          equalp (App t1 t2)  (App t1' t2')    = t1 == t1' && t2 == t2'
          equalp (TConst c)   (TConst c')      = c == c'
          equalp (Proj tm i)  (Proj tm' i')    = tm == tm' && i == i'
          equalp Erased       Erased           = True
          equalp Impossible   Impossible       = True
          equalp (TType u)    (TType u')       = u == u'
          equalp x            y                = False

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

    %assert_total
    fe : List TTName -> TT -> Maybe Raw
    fe env (P _ n _)     = Just $ Var n
    fe env (V i)         = map Var (atIndex env i)
    fe env (Bind n b sc) = [| RBind (pure n) (traverse (fe env) b) (fe (n::env) sc) |]
    fe env (App f a)     = [| RApp (fe env f) (fe env a) |]
    fe env (TConst c)    = Just $ RConstant c
    fe env (Proj tm i)   = Nothing -- runtime only, not useful for metaprogramming
    fe env (TType i)     = Just RType
    fe env Erased        = Just $ RConstant Forgot
    fe env Impossible    = Nothing

instance Show Raw where
  show r = my_show r
    where %assert_total my_show : Raw -> String
          my_show (Var n) = "Var " ++ show n
          my_show (RBind n b tm) = "RBind " ++ show n ++ " " ++ show b ++ " (" ++ my_show tm ++ ")"
          my_show (RApp tm tm') = "RApp " ++ my_show tm ++ " " ++ my_show tm'
          my_show RType = "RType"
          my_show (RForce tm) = "RForce " ++ my_show tm
          my_show (RConstant c) = "RConstant " ++ show c

instance Show SourceLocation where
  show (FileLoc filename line col) = "FileLoc \"" ++ filename ++ "\" " ++ show line ++ " " ++ show col

instance Show Err where
  show (Msg x) = "Msg \"" ++ x ++ "\""
  show (InternalMsg x) = "InternalMsg \"" ++ x ++ "\""
  show (CantUnify x tm tm' err xs y) = "CantUnify " ++ show x ++
                                       " ( " ++ show tm ++ ") (" ++ show tm' ++ ") (" ++ show err ++ ") " ++
                                       show xs ++ " " ++ show y
  show (InfiniteUnify n tm xs) = "InfiniteUnify " ++ show n ++ show tm ++ show xs
  show (CantConvert tm tm' xs) = "CantConvert " ++ show tm ++ show tm' ++ show xs
  show (CantSolveGoal tm ctxt) = "CantSolveGoal " ++ show tm ++ " " ++ show ctxt
  show (UnifyScope n n' tm xs) = "UnifyScope " ++ show n ++ " " ++ show n' ++ " " ++ show tm ++ " " ++ show xs
  show (CantInferType x) = "CantInferType " ++ show x
  show (NonFunctionType tm tm') = "NonFunctionType " ++ show tm ++ show tm'
  show (NotEquality tm tm') = "NotEquality " ++ show tm ++ " " ++ show tm'
  show (TooManyArguments n) = "TooManyArguments " ++ show n
  show (CantIntroduce tm) = "CantIntroduce " ++ show tm
  show (NoSuchVariable n) = "NoSuchVariable " ++ show n
  show (WithFnType tm) = "WithFnType " ++ show tm
  show (CantMatch tm) = "CantMatch " ++ show tm
  show (NoTypeDecl n) = "NoTypeDecl " ++ show n
  show (NotInjective tm tm' x) = "NotInjective " ++ show tm ++ " " ++ show tm'
  show (CantResolve tm) = "CantResolve " ++ show tm
  show (CantResolveAlts xs) = "CantResolveAlts " ++ show xs
  show (IncompleteTerm tm) = "IncompleteTerm " ++ show tm
  show UniverseError = "UniverseError"
  show ProgramLineComment = "ProgramLineComment"
  show (Inaccessible n) = "Inaccessible " ++ show n
  show (NonCollapsiblePostulate n) = "NonCollapsiblePostulate " ++ show n
  show (AlreadyDefined n) = "AlreadyDefined " ++ show n
  show (ProofSearchFail err) = "ProofSearchFail " ++ show err
  show (NoRewriting tm) = "NoRewriting " ++ show tm
  show (ProviderError x) = "ProviderError \"" ++ show x ++ "\""
  show (LoadingFailed x err) = "LoadingFailed " ++ show x ++ " (" ++ show err ++ ")"


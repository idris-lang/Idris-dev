module Language.Reflection.Utils

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
binderTy (Pi t)        = t
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
  show IType      = "IType"
  show BIType     = "BIType"
  show FlType     = "FlType"
  show ChType     = "ChType"
  show StrType    = "StrType"
  show (B8 b)     = "(B8 ...)"
  show (B16 b)    = "(B16 ...)"
  show (B32 b)    = "(B32 ...)"
  show (B64 b)    = "(B64 ...)"
  show B8Type     = "B8Type"
  show B16Type    = "B16Type"
  show B32Type    = "B32Type"
  show B64Type    = "B64Type"
  show PtrType    = "PtrType"
  show VoidType   = "VoidType"
  show Forgot     = "Forgot"

instance Eq Const where
  (I i)     == (I i')      = i == i'
  (BI n)    == (BI n')     = n == n'
  (Fl f)    == (Fl f')     = f == f'
  (Ch c)    == (Ch c')     = c == c'
  (Str str) == (Str str')  = str == str'
  IType     == IType       = True
  BIType    == BIType      = True
  FlType    == FlType      = True
  ChType    == ChType      = True
  StrType   == StrType     = True
  (B8 b)    == (B8 b')     = False -- FIXME: b == b'
  (B16 b)   == (B16 b')    = False -- FIXME: b == b'
  (B32 b)   == (B32 b')    = False -- FIXME: b == b'
  (B64 b)   == (B64 b')    = False -- FIXME: b == b'
  B8Type    == B8Type      = True
  B16Type   == B16Type     = True
  B32Type   == B32Type     = True
  B64Type   == B64Type     = True
  PtrType   == PtrType     = True
  VoidType  == VoidType    = True
  Forgot    == Forgot      = True
  x         == y           = False

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
  show (Pi t) = "(Pi " ++ show t ++ ")"
  show (Let t1 t2) = "(Let " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (NLet t1 t2) = "(NLet " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Hole t) = "(Hole " ++ show t ++ ")"
  show (GHole t) = "(GHole " ++ show t ++ ")"
  show (Guess t1 t2) = "(Guess " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (PVar t) = "(PVar " ++ show t ++ ")"
  show (PVTy t) = "(PVTy " ++ show t ++ ")"

instance (Eq a) => Eq (Binder a) where
  (Lam t)       == (Lam t')         = t == t'
  (Pi t)        == (Pi t')          = t == t'
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

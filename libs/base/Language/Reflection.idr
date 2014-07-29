module Language.Reflection

%access public

data TTName = UN String
            -- ^ User-provided name
            | NS TTName (List String)
            -- ^ Root, namespaces
            | MN Int String
            -- ^ Machine chosen names
            | NErased
            -- ^ Name of somethng which is never used in scope
%name TTName n, n'

implicit
userSuppliedName : String -> TTName
userSuppliedName = UN

data TTUExp = UVar Int
            -- ^ universe variable
            | UVal Int
            -- ^ explicit universe variable
%name TTUExp uexp

data NativeTy = IT8 | IT16 | IT32 | IT64

data IntTy = ITFixed NativeTy | ITNative | ITBig | ITChar
           | ITVec NativeTy Int

data ArithTy = ATInt Language.Reflection.IntTy | ATFloat

||| Primitive constants
data Const = I Int | BI Integer | Fl Float | Ch Char | Str String
           | B8 Bits8 | B16 Bits16 | B32 Bits32 | B64 Bits64
           | B8V Bits8x16 | B16V Bits16x8
           | B32V Bits32x4 | B64V Bits64x2
           | AType ArithTy | StrType
           | PtrType | ManagedPtrType | BufferType | VoidType | Forgot

%name Const c, c'

abstract class ReflConst (a : Type) where
   toConst : a -> Const

instance ReflConst Int where
   toConst x = I x

instance ReflConst Integer where
   toConst = BI

instance ReflConst Float where
   toConst = Fl

instance ReflConst Char where
   toConst = Ch

instance ReflConst String where
   toConst = Str

instance ReflConst Bits8 where
   toConst = B8

instance ReflConst Bits16 where
   toConst = B16

instance ReflConst Bits32 where
   toConst = B32

instance ReflConst Bits64 where
   toConst = B64

implicit
reflectConstant: (ReflConst a) => a -> Const
reflectConstant = toConst


||| Types of named references
data NameType = Bound
              -- ^ reference which is just bound, e.g. by intro
              | Ref
              -- ^ reference to a variable
              | DCon Int Int
              -- ^ constructor with tag and number
              | TCon Int Int
              -- ^ type constructor with tag and number
%name NameType nt, nt'

||| Types annotations for bound variables in different
||| binding contexts
data Binder a = Lam a
              | Pi a
              | Let a a
              | NLet a a
              | Hole a
              | GHole a
              | Guess a a
              | PVar a
              | PVTy a
%name Binder b, b'

instance Functor Binder where
  map f (Lam x) = Lam (f x)
  map f (Pi x) = Pi (f x)
  map f (Let x y) = Let (f x) (f y)
  map f (NLet x y) = NLet (f x) (f y)
  map f (Hole x) = Hole (f x)
  map f (GHole x) = GHole (f x)
  map f (Guess x y) = Guess (f x) (f y)
  map f (PVar x) = PVar (f x)
  map f (PVTy x) = PVTy (f x)

instance Foldable Binder where
  foldr f z (Lam x) = f x z
  foldr f z (Pi x) = f x z
  foldr f z (Let x y) = f x (f y z)
  foldr f z (NLet x y) = f x (f y z)
  foldr f z (Hole x) = f x z
  foldr f z (GHole x) = f x z
  foldr f z (Guess x y) = f x (f y z)
  foldr f z (PVar x) = f x z
  foldr f z (PVTy x) = f x z

instance Traversable Binder where
  traverse f (Lam x) = [| Lam (f x) |]
  traverse f (Pi x) = [| Pi (f x) |]
  traverse f (Let x y) = [| Let (f x) (f y) |]
  traverse f (NLet x y) = [| NLet (f x) (f y) |]
  traverse f (Hole x) = [| Hole (f x) |]
  traverse f (GHole x) = [| GHole (f x) |]
  traverse f (Guess x y) = [| Guess (f x) (f y) |]
  traverse f (PVar x) = [| PVar (f x) |]
  traverse f (PVTy x) = [| PVTy (f x) |]


||| Reflection of the well typed core language
data TT = P NameType TTName TT
        -- ^ named binders
        | V Int
        -- ^ variables
        | Bind TTName (Binder TT) TT
        -- ^ type annotated named bindings
        | App TT TT
        -- ^ (named) application of a function to a value
        | TConst Const
        -- ^ constants
        | Proj TT Int
        -- ^ argument projection; runtime only
        | Erased
        -- ^ erased terms
        | Impossible
        -- ^ impossible terms
        | TType TTUExp
        -- ^ types

%name TT tm, tm'

||| Raw terms without types
data Raw = Var TTName
         | RBind TTName (Binder Raw) Raw
         | RApp Raw Raw
         | RType
         | RForce Raw
         | RConstant Const

%name Raw tm, tm'

||| Error reports are a list of report parts
data ErrorReportPart = TextPart String
                     | NamePart TTName
                     | TermPart TT
                     | SubReport (List ErrorReportPart)
%name ErrorReportPart part, p

data Tactic = Try Tactic Tactic
            -- ^ try the first tactic and resort to the second one on failure
            | GoalType String Tactic
            -- ^ only run if the goal has the right type
            | Refine TTName
            -- ^ resolve function name, find matching arguments in the
            -- context and compute the proof target
            | Seq Tactic Tactic
            -- ^ apply both tactics in sequence
            | Trivial
            -- ^ intelligently construct the proof target from the context
            | Search Int
            -- ^ build a proof by applying contructors up to a maximum depth 
            | Instance
            -- ^ resolve a type class 
            | Solve
            -- ^ infer the proof target from the context
            | Intros
            -- ^ introduce all variables into the context
            | Intro TTName
            -- ^ introduce a named variable into the context, use the
            -- first one if the given name is not found
            | ApplyTactic TT
            -- ^ invoke the reflected rep. of another tactic
            | Reflect TT
            -- ^ turn a value into its reflected representation
            | ByReflection TT
            -- ^ use a %reflection function
            | Fill Raw
            -- ^ turn a raw value back into a term
            | Exact TT
            -- ^ use the given value to conclude the proof
            | Focus TTName
            -- ^ focus a named hole
            | Rewrite TT
            -- ^ rewrite using the reflected rep. of a equality proof
            | Induction TT
            -- ^ do induction on the particular expression
            | Case TT
            -- ^ do case analysis on particular expression
            | LetTac TTName TT
            -- ^ name a reflected term
            | LetTacTy TTName TT TT
            -- ^ name a reflected term and type it
            | Compute
            -- ^ normalise the context
            | Skip
            -- ^ do nothing
            | Fail (List ErrorReportPart)
%name Tactic tac, tac'


class Quotable a where
  quotedTy : TT
  quote : a -> TT

instance Quotable Nat where
  quotedTy = `(Nat)

  quote Z     = `(Z)
  quote (S k) = `(S ~(quote k))

instance Quotable Int where
  quotedTy = `(Int)
  quote x = TConst (I x)

instance Quotable Float where
  quotedTy = `(Float)
  quote x = TConst (Fl x)

instance Quotable Char where
  quotedTy = `(Char)
  quote x = TConst (Ch x)

instance Quotable Bits8 where
  quotedTy = `(Bits8)
  quote x = TConst (B8 x)

instance Quotable Bits16 where
  quotedTy = `(Bits16)
  quote x = TConst (B16 x)

instance Quotable Bits32 where
  quotedTy = `(Bits32)
  quote x = TConst (B32 x)

instance Quotable Bits64 where
  quotedTy = `(Bits64)
  quote x = TConst (B64 x)

instance Quotable Integer where
  quotedTy = `(Integer)
  quote x = TConst (BI x)

instance Quotable Bits8x16 where
  quotedTy = `(Bits8x16)
  quote x = TConst (B8V x)

instance Quotable Bits16x8 where
  quotedTy = `(Bits16x8)
  quote x = TConst (B16V x)

instance Quotable Bits32x4 where
  quotedTy = `(Bits32x4)
  quote x = TConst (B32V x)

instance Quotable Bits64x2 where
  quotedTy = `(Bits64x2)
  quote x = TConst (B64V x)

instance Quotable String where
  quotedTy = `(String)
  quote x = TConst (Str x)

instance Quotable NameType where
  quotedTy = `(NameType)
  quote Bound = `(Bound)
  quote Ref = `(Ref)
  quote (DCon x y) = `(DCon ~(quote x) ~(quote y))
  quote (TCon x y) = `(TCon ~(quote x) ~(quote y))

instance Quotable a => Quotable (List a) where
  quotedTy = `(List ~(quotedTy {a=a}))
  quote [] = `(List.Nil {a=~quotedTy})
  quote (x :: xs) = `(List.(::) {a=~quotedTy} ~(quote x) ~(quote xs))

instance Quotable TTName where
  quotedTy = `(TTName)
  quote (UN x) = `(UN ~(quote x))
  quote (NS n xs) = `(NS ~(quote n) ~(quote xs))
  quote (MN x y) = `(MN ~(quote x) ~(quote y))
  quote NErased = `(NErased)

instance Quotable NativeTy where
    quotedTy = `(NativeTy)
    quote IT8 = `(Reflection.IT8)
    quote IT16 = `(Reflection.IT16)
    quote IT32 = `(Reflection.IT32)
    quote IT64 = `(Reflection.IT64)

instance Quotable Reflection.IntTy where
  quotedTy = `(Reflection.IntTy)
  quote (ITFixed x) = `(ITFixed ~(quote x))
  quote ITNative = `(Reflection.ITNative)
  quote ITBig = `(ITBig)
  quote ITChar = `(Reflection.ITChar)
  quote (ITVec x y) = `(ITVec ~(quote x) ~(quote y))

instance Quotable ArithTy where
  quotedTy = `(ArithTy)
  quote (ATInt x) = `(ATInt ~(quote x))
  quote ATFloat = `(ATFloat)

instance Quotable Const where
  quotedTy = `(Const)
  quote (I x) = `(I ~(quote x))
  quote (BI x) = `(BI ~(quote x))
  quote (Fl x) = `(Fl ~(quote x))
  quote (Ch x) = `(Ch ~(quote x))
  quote (Str x) = `(Str ~(quote x))
  quote (B8 x) = `(B8 ~(quote x))
  quote (B16 x) = `(B16 ~(quote x))
  quote (B32 x) = `(B32 ~(quote x))
  quote (B64 x) = `(B64 ~(quote x))
  quote (B8V xs) = `(B8V ~(quote xs))
  quote (B16V xs) = `(B16V ~(quote xs))
  quote (B32V xs) = `(B32V ~(quote xs))
  quote (B64V xs) = `(B64V ~(quote xs))
  quote (AType x) = `(AType ~(quote x))
  quote StrType = `(StrType)
  quote PtrType = `(PtrType)
  quote ManagedPtrType = `(ManagedPtrType)
  quote BufferType = `(BufferType)
  quote VoidType = `(VoidType)
  quote Forgot = `(Forgot)


instance Quotable TTUExp where
  quotedTy = `(TTUExp)
  quote (UVar x) = `(UVar ~(quote x))
  quote (UVal x) = `(UVal ~(quote x))

mutual
  instance Quotable TT where
    quotedTy = `(TT)
    quote (P nt n tm) = `(P ~(quote nt) ~(quote n) ~(quote tm))
    quote (V x) = `(V ~(quote x))
    quote (Bind n b tm) = `(Bind ~(quote n) ~(assert_total (quote b)) ~(quote tm))
    quote (App f x) = `(App ~(quote f) ~(quote x))
    quote (TConst c) = `(TConst ~(quote c))
    quote (Proj tm x) = `(Proj ~(quote tm) ~(quote x))
    quote Erased = `(Erased)
    quote Impossible = `(Impossible)
    quote (TType uexp) = `(TType ~(quote uexp))

  instance Quotable (Binder TT) where
    quotedTy = `(Binder TT)
    quote (Lam x) = `(Lam {a=TT} ~(assert_total (quote x)))
    quote (Pi x) = `(Pi {a=TT} ~(assert_total (quote x)))
    quote (Let x y) = `(Let {a=TT} ~(assert_total (quote x))
                                           ~(assert_total (quote y)))
    quote (NLet x y) = `(NLet {a=TT} ~(assert_total (quote x))
                                           ~(assert_total (quote y)))
    quote (Hole x) = `(Hole {a=TT} ~(assert_total (quote x)))
    quote (GHole x) = `(GHole {a=TT} ~(assert_total (quote x)))
    quote (Guess x y) = `(Guess {a=TT} ~(assert_total (quote x))
                                             ~(assert_total (quote y)))
    quote (PVar x) = `(PVar {a=TT} ~(assert_total (quote x)))
    quote (PVTy x) = `(PVTy {a=TT} ~(assert_total (quote x)))



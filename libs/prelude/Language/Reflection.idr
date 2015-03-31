module Language.Reflection

import Builtins
import Prelude.Applicative
import Prelude.Basics
import Prelude.Foldable
import Prelude.Functor
import Prelude.List
import Prelude.Nat
import Prelude.Traversable

%access public

data TTName =
            ||| A user-provided name
            UN String |
            ||| A name in some namespace.
            |||
            ||| The namespace is in reverse order, so `(NS (UN "foo") ["B", "A"])` represents the name `A.B.foo`
            NS TTName (List String) |
            ||| Machine-chosen names
            MN Int String |
            ||| Name of something which is never used in scope
            NErased
%name TTName n, n'

implicit
userSuppliedName : String -> TTName
userSuppliedName = UN

data TTUExp =
            ||| Universe variable
            UVar Int |
            ||| Explicit universe level
            UVal Int
%name TTUExp uexp

data NativeTy = IT8 | IT16 | IT32 | IT64

data IntTy = ITFixed NativeTy | ITNative | ITBig | ITChar

data ArithTy = ATInt Language.Reflection.IntTy | ATFloat

||| Primitive constants
data Const = I Int | BI Integer | Fl Float | Ch Char | Str String
           | B8 Bits8 | B16 Bits16 | B32 Bits32 | B64 Bits64
           | AType ArithTy | StrType
           | VoidType | Forgot
           | WorldType | TheWorld
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
data NameType =
  ||| A reference which is just bound, e.g. by intro
  Bound |
  ||| A reference to a de Bruijn-indexed variable
  Ref |
  ||| Data constructor with tag and number
  DCon Int Int |
  ||| Type constructor with tag and number
  TCon Int Int

%name NameType nt, nt'

||| Types annotations for bound variables in different
||| binding contexts
data Binder a = Lam a
              | Pi a a
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
  map f (Pi x k) = Pi (f x) (f k)
  map f (Let x y) = Let (f x) (f y)
  map f (NLet x y) = NLet (f x) (f y)
  map f (Hole x) = Hole (f x)
  map f (GHole x) = GHole (f x)
  map f (Guess x y) = Guess (f x) (f y)
  map f (PVar x) = PVar (f x)
  map f (PVTy x) = PVTy (f x)

instance Foldable Binder where
  foldr f z (Lam x) = f x z
  foldr f z (Pi x k) = f x (f k z)
  foldr f z (Let x y) = f x (f y z)
  foldr f z (NLet x y) = f x (f y z)
  foldr f z (Hole x) = f x z
  foldr f z (GHole x) = f x z
  foldr f z (Guess x y) = f x (f y z)
  foldr f z (PVar x) = f x z
  foldr f z (PVTy x) = f x z

instance Traversable Binder where
  traverse f (Lam x) = [| Lam (f x) |]
  traverse f (Pi x k) = [| Pi (f x) (f k) |]
  traverse f (Let x y) = [| Let (f x) (f y) |]
  traverse f (NLet x y) = [| NLet (f x) (f y) |]
  traverse f (Hole x) = [| Hole (f x) |]
  traverse f (GHole x) = [| GHole (f x) |]
  traverse f (Guess x y) = [| Guess (f x) (f y) |]
  traverse f (PVar x) = [| PVar (f x) |]
  traverse f (PVTy x) = [| PVTy (f x) |]

||| Universes
data Universe = NullType | UniqueType | AllTypes

||| Reflection of the well typed core language
data TT =
        ||| A reference to some name (P for Parameter)
        P NameType TTName TT |
        ||| de Bruijn variables
        V Int |
        ||| Bind a variable
        Bind TTName (Binder TT) TT |
        ||| Apply one term to another
        App TT TT |
        ||| Embed a constant
        TConst Const |
        ||| Argument projection; runtime only
        Proj TT Int |
        ||| Erased terms
        Erased |
        ||| Impossible terms
        Impossible |
        ||| The type of types along (with universe constraints)
        TType TTUExp |
        UType Universe
%name TT tm, tm'

||| Raw terms without types
data Raw =
         ||| Variables, global or local
         Var TTName |
         ||| Bind a variable
         RBind TTName (Binder Raw) Raw |
         ||| Application
         RApp Raw Raw |
         ||| The type of types
         RType |
         RUType Universe |
         RForce Raw |
         ||| Embed a constant
         RConstant Const
%name Raw tm, tm'

data SourceLocation : Type where
  FileLoc : (filename : String) -> (start : (Int, Int)) -> (end : (Int, Int)) -> SourceLocation

%name SourceLocation loc

||| Error reports are a list of report parts
data ErrorReportPart =
                     ||| A human-readable string
                     TextPart String |
                     ||| An Idris name (to be semantically coloured)
                     NamePart TTName |
                     ||| An Idris term, to be pretty printed
                     TermPart TT |
                     ||| An indented sub-report, to provide more details
                     SubReport (List ErrorReportPart)
%name ErrorReportPart part, p

||| A representation of Idris's tactics that can be returned from custom
||| tactic implementations. Generate these using `applyTactic`.
data Tactic =
            ||| Try the first tactic and resort to the second one on failure
            Try Tactic Tactic |
            ||| Only run if the goal has the right type
            GoalType String Tactic |
            ||| Resolve function name, find matching arguments in the
            ||| context and compute the proof target
            Refine TTName |
            ||| Apply both tactics in sequence
            Seq Tactic Tactic |
            ||| Introduce a new hole with a particular type
            Claim TTName TT |
            ||| Move the current hole to the end
            Unfocus |
            ||| Intelligently construct the proof target from the context
            Trivial |
            ||| Build a proof by applying contructors up to a maximum depth
            Search Int |
            ||| Resolve a type class
            Instance |
            ||| Infer the proof target from the context
            Solve |
            ||| introduce all variables into the context
            Intros |
            ||| Introduce a named variable into the context, use the
            ||| first one if the given name is not found
            Intro TTName |
            ||| Invoke the reflected rep. of another tactic
            ApplyTactic TT |
            ||| Turn a value into its reflected representation
            Reflect TT |
            ||| Use a `%reflection` function
            ByReflection TT |
            ||| Turn a raw value back into a term
            Fill Raw |
            ||| Use the given value to conclude the proof
            Exact TT |
            ||| Focus on a particular hole
            Focus TTName |
            ||| Rewrite with an equality
            Rewrite TT |
            ||| Perform induction on a particular expression
            Induction TT |
            ||| Perform case analysis on a particular expression
            Case TT |
            ||| Name a reflected term
            LetTac TTName TT |
            ||| Name a reflected term and type it
            LetTacTy TTName TT TT |
            ||| Normalise the goal
            Compute |
            ||| Do nothing
            Skip |
            ||| Fail with an error message
            Fail (List ErrorReportPart) |
            ||| Attempt to fill the hole with source code information
            SourceFC
%name Tactic tac, tac'


||| Things with a canonical representation as a reflected term.
|||
||| This type class is intended to be used during proof automation and the
||| construction of custom tactics.
|||
||| @ a the type to be quoted
||| @ t the type to quote it to (typically `TT` or `Raw`)
class Quotable a t where
  ||| A representation of the type `a`.
  |||
  ||| This is to enable quoting polymorphic datatypes
  quotedTy : t

  ||| Quote a particular element of `a`.
  |||
  ||| Each equation should look something like ```quote (Foo x y) = `(Foo ~(quote x) ~(quote y))```
  quote : a -> t

instance Quotable Nat TT where
  quotedTy = `(Nat)

  quote Z     = `(Z)
  quote (S k) = `(S ~(quote k))

instance Quotable Nat Raw where
  quotedTy = `(Nat)

  quote Z     = `(Z)
  quote (S k) = `(S ~(quote k))

instance Quotable Int TT where
  quotedTy = `(Int)
  quote x = TConst (I x)

instance Quotable Int Raw where
  quotedTy = `(Int)
  quote x = RConstant (I x)

instance Quotable Float TT where
  quotedTy = `(Float)
  quote x = TConst (Fl x)

instance Quotable Float Raw where
  quotedTy = `(Float)
  quote x = RConstant (Fl x)

instance Quotable Char TT where
  quotedTy = `(Char)
  quote x = TConst (Ch x)

instance Quotable Char Raw where
  quotedTy = `(Char)
  quote x = RConstant (Ch x)

instance Quotable Bits8 TT where
  quotedTy = `(Bits8)
  quote x = TConst (B8 x)

instance Quotable Bits8 Raw where
  quotedTy = `(Bits8)
  quote x = RConstant (B8 x)

instance Quotable Bits16 TT where
  quotedTy = `(Bits16)
  quote x = TConst (B16 x)

instance Quotable Bits16 Raw where
  quotedTy = `(Bits16)
  quote x = RConstant (B16 x)

instance Quotable Bits32 TT where
  quotedTy = `(Bits32)
  quote x = TConst (B32 x)

instance Quotable Bits32 Raw where
  quotedTy = `(Bits32)
  quote x = RConstant (B32 x)

instance Quotable Bits64 TT where
  quotedTy = `(Bits64)
  quote x = TConst (B64 x)

instance Quotable Bits64 Raw where
  quotedTy = `(Bits64)
  quote x = RConstant (B64 x)

instance Quotable Integer TT where
  quotedTy = `(Integer)
  quote x = TConst (BI x)

instance Quotable Integer Raw where
  quotedTy = `(Integer)
  quote x = RConstant (BI x)

instance Quotable String TT where
  quotedTy = `(String)
  quote x = TConst (Str x)

instance Quotable String Raw where
  quotedTy = `(String)
  quote x = RConstant (Str x)

instance Quotable NameType TT where
  quotedTy = `(NameType)
  quote Bound = `(Bound)
  quote Ref = `(Ref)
  quote (DCon x y) = `(DCon ~(quote x) ~(quote y))
  quote (TCon x y) = `(TCon ~(quote x) ~(quote y))

instance Quotable NameType Raw where
  quotedTy = `(NameType)
  quote Bound = `(Bound)
  quote Ref = `(Ref)
  quote (DCon x y) = `(DCon ~(quote {t=Raw} x) ~(quote {t=Raw} y))
  quote (TCon x y) = `(TCon ~(quote {t=Raw} x) ~(quote {t=Raw} y))

instance Quotable a TT => Quotable (List a) TT where
  quotedTy = `(List ~(quotedTy {a}))
  quote [] = `(List.Nil {a=~(quotedTy {a})})
  quote (x :: xs) = `(List.(::) {a=~(quotedTy {a})} ~(quote x) ~(quote xs))

instance Quotable a Raw => Quotable (List a) Raw where
  quotedTy = `(List ~(quotedTy {a}))
  quote [] = `(List.Nil {a=~(quotedTy {a})})
  quote (x :: xs) = `(List.(::) {a=~(quotedTy {a})} ~(quote x) ~(quote xs))

instance Quotable TTName TT where
  quotedTy = `(TTName)
  quote (UN x) = `(UN ~(quote x))
  quote (NS n xs) = `(NS ~(quote n) ~(quote xs))
  quote (MN x y) = `(MN ~(quote x) ~(quote y))
  quote NErased = `(NErased)

instance Quotable TTName Raw where
  quotedTy = `(TTName)
  quote (UN x) = `(UN ~(quote {t=Raw} x))
  quote (NS n xs) = `(NS ~(quote {t=Raw} n) ~(quote {t=Raw} xs))
  quote (MN x y) = `(MN ~(quote {t=Raw} x) ~(quote {t=Raw} y))
  quote NErased = `(NErased)

instance Quotable NativeTy TT where
    quotedTy = `(NativeTy)
    quote IT8 = `(Reflection.IT8)
    quote IT16 = `(Reflection.IT16)
    quote IT32 = `(Reflection.IT32)
    quote IT64 = `(Reflection.IT64)

instance Quotable NativeTy Raw where
    quotedTy = `(NativeTy)
    quote IT8 = `(Reflection.IT8)
    quote IT16 = `(Reflection.IT16)
    quote IT32 = `(Reflection.IT32)
    quote IT64 = `(Reflection.IT64)

instance Quotable Reflection.IntTy TT where
  quotedTy = `(Reflection.IntTy)
  quote (ITFixed x) = `(ITFixed ~(quote x))
  quote ITNative = `(Reflection.ITNative)
  quote ITBig = `(ITBig)
  quote ITChar = `(Reflection.ITChar)

instance Quotable Reflection.IntTy Raw where
  quotedTy = `(Reflection.IntTy)
  quote (ITFixed x) = `(ITFixed ~(quote {t=Raw} x))
  quote ITNative = `(Reflection.ITNative)
  quote ITBig = `(ITBig)
  quote ITChar = `(Reflection.ITChar)

instance Quotable ArithTy TT where
  quotedTy = `(ArithTy)
  quote (ATInt x) = `(ATInt ~(quote x))
  quote ATFloat = `(ATFloat)

instance Quotable ArithTy Raw where
  quotedTy = `(ArithTy)
  quote (ATInt x) = `(ATInt ~(quote {t=Raw} x))
  quote ATFloat = `(ATFloat)

instance Quotable Const TT where
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
  quote (AType x) = `(AType ~(quote x))
  quote StrType = `(StrType)
  quote VoidType = `(VoidType)
  quote Forgot = `(Forgot)
  quote WorldType = `(WorldType)
  quote TheWorld = `(TheWorld)

instance Quotable Const Raw where
  quotedTy = `(Const)
  quote (I x) = `(I ~(quote {t=Raw} x))
  quote (BI x) = `(BI ~(quote {t=Raw} x))
  quote (Fl x) = `(Fl ~(quote {t=Raw} x))
  quote (Ch x) = `(Ch ~(quote {t=Raw} x))
  quote (Str x) = `(Str ~(quote {t=Raw} x))
  quote (B8 x) = `(B8 ~(quote {t=Raw} x))
  quote (B16 x) = `(B16 ~(quote {t=Raw} x))
  quote (B32 x) = `(B32 ~(quote {t=Raw} x))
  quote (B64 x) = `(B64 ~(quote {t=Raw} x))
  quote (AType x) = `(AType ~(quote {t=Raw} x))
  quote StrType = `(StrType)
  quote VoidType = `(VoidType)
  quote Forgot = `(Forgot)
  quote WorldType = `(WorldType)
  quote TheWorld = `(TheWorld)

instance Quotable TTUExp TT where
  quotedTy = `(TTUExp)
  quote (UVar x) = `(UVar ~(quote x))
  quote (UVal x) = `(UVal ~(quote x))

instance Quotable TTUExp Raw where
  quotedTy = `(TTUExp)
  quote (UVar x) = `(UVar ~(quote {t=Raw} x))
  quote (UVal x) = `(UVal ~(quote {t=Raw} x))

instance Quotable Universe TT where
  quotedTy = `(Universe)
  quote Reflection.NullType = `(NullType)
  quote Reflection.UniqueType = `(UniqueType)
  quote Reflection.AllTypes = `(AllTypes)

instance Quotable Universe Raw where
  quotedTy = `(Universe)
  quote Reflection.NullType = `(NullType)
  quote Reflection.UniqueType = `(UniqueType)
  quote Reflection.AllTypes = `(AllTypes)

mutual
  instance Quotable TT TT where
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
    quote (UType u) = `(UType ~(quote u))

  instance Quotable (Binder TT) TT where
    quotedTy = `(Binder TT)
    quote (Lam x) = `(Lam {a=TT} ~(assert_total (quote x)))
    quote (Pi x k) = `(Pi {a=TT} ~(assert_total (quote x))
                                 ~(assert_total (quote k)))
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


instance Quotable ErrorReportPart TT where
  quotedTy = `(ErrorReportPart)
  quote (TextPart x) = `(TextPart ~(quote x))
  quote (NamePart n) = `(NamePart ~(quote n))
  quote (TermPart tm) = `(TermPart ~(quote tm))
  quote (SubReport xs) = `(SubReport ~(assert_total $ quote xs))

mutual
  quoteRaw : Raw -> TT
  quoteRaw (Var n) = `(Var ~(quote n))
  quoteRaw (RBind n b tm) = `(RBind ~(quote n) ~(assert_total $ quoteRawBinder b) ~(quoteRaw tm))
  quoteRaw (RApp tm tm') = `(RApp ~(quoteRaw tm) ~(quoteRaw tm'))
  quoteRaw RType = `(RType)
  quoteRaw (RUType u) = `(RUType ~(quote u))
  quoteRaw (RForce tm) = `(RForce ~(quoteRaw tm))
  quoteRaw (RConstant c) = `(RConstant ~(quote c))

  quoteRawBinder : Binder Raw -> TT
  quoteRawBinder (Lam x) = `(Lam {a=Raw} ~(quoteRaw x))
  quoteRawBinder (Pi x k) = `(Pi {a=Raw} ~(quoteRaw x) ~(quoteRaw k))
  quoteRawBinder (Let x y) = `(Let {a=Raw} ~(quoteRaw x) ~(quoteRaw y))
  quoteRawBinder (NLet x y) = `(NLet {a=Raw} ~(quoteRaw x) ~(quoteRaw y))
  quoteRawBinder (Hole x) = `(Hole {a=Raw} ~(quoteRaw x))
  quoteRawBinder (GHole x) = `(GHole {a=Raw} ~(quoteRaw x))
  quoteRawBinder (Guess x y) = `(Guess {a=Raw} ~(quoteRaw x) ~(quoteRaw y))
  quoteRawBinder (PVar x) = `(PVar {a=Raw} ~(quoteRaw x))
  quoteRawBinder (PVTy x) = `(PVTy {a=Raw} ~(quoteRaw x))

instance Quotable Raw TT where
  quotedTy = `(Raw)
  quote = quoteRaw

instance Quotable (Binder Raw) TT where
  quotedTy = `(Binder Raw)
  quote = quoteRawBinder

instance Quotable Tactic TT where
  quotedTy = `(Tactic)
  quote (Try tac tac') = `(Try ~(quote tac) ~(quote tac'))
  quote (GoalType x tac) = `(GoalType ~(quote x) ~(quote tac))
  quote (Refine n) = `(Refine ~(quote n))
  quote (Claim n ty) = `(Claim ~(quote n) ~(quote ty))
  quote Unfocus = `(Unfocus)
  quote (Seq tac tac') = `(Seq ~(quote tac) ~(quote tac'))
  quote Trivial = `(Trivial)
  quote (Search x) = `(Search ~(quote x))
  quote Instance = `(Instance)
  quote Solve = `(Solve)
  quote Intros = `(Intros)
  quote (Intro n) = `(Intro ~(quote n))
  quote (ApplyTactic tm) = `(ApplyTactic ~(quote tm))
  quote (Reflect tm) = `(Reflect ~(quote tm))
  quote (ByReflection tm) = `(ByReflection ~(quote tm))
  quote (Fill tm) = `(Fill ~(quote tm))
  quote (Exact tm) = `(Exact ~(quote tm))
  quote (Focus n) = `(Focus ~(quote n))
  quote (Rewrite tm) = `(Rewrite ~(quote tm))
  quote (Induction tm) = `(Induction ~(quote tm))
  quote (Case tm) = `(Case ~(quote tm))
  quote (LetTac n tm) = `(LetTac ~(quote n) ~(quote tm))
  quote (LetTacTy n tm tm') = `(LetTacTy ~(quote n) ~(quote tm) ~(quote tm'))
  quote Compute = `(Compute)
  quote Skip = `(Skip)
  quote (Fail xs) = `(Fail ~(quote xs))
  quote SourceFC = `(SourceFC)


instance Quotable SourceLocation TT where
  quotedTy = `(SourceLocation)
  quote (FileLoc fn (sl, sc) (el, ec)) =
    `(FileLoc ~(quote fn)
              (~(quote sl), ~(quote sc))
              (~(quote el), ~(quote ec)))

instance Quotable SourceLocation Raw where
  quotedTy = `(SourceLocation)
  quote (FileLoc fn (sl, sc) (el, ec)) =
    `(FileLoc ~(quote {t=Raw} fn)
              (~(quote {t=Raw} sl), ~(quote {t=Raw} sc))
              (~(quote {t=Raw} el), ~(quote {t=Raw} ec)))

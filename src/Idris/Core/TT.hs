{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, DeriveFunctor #-}

{-| TT is the core language of Idris. The language has:

   * Full dependent types

   * A hierarchy of universes, with cumulativity: Type : Type1, Type1 : Type2, ...

   * Pattern matching letrec binding

   * (primitive types defined externally)

   Some technical stuff:

   * Typechecker is kept as simple as possible - no unification, just a checker for incomplete terms.

   * We have a simple collection of tactics which we use to elaborate source
     programs with implicit syntax into fully explicit terms.
-}

module Idris.Core.TT(module Idris.Core.TT, module Idris.Core.TC) where

import Idris.Core.TC

import Control.Monad.State.Strict
import Control.Monad.Trans.Error (Error(..))
import Debug.Trace
import qualified Data.Map.Strict as Map
import Data.Char
import qualified Data.Text as T
import Data.List
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as V
import qualified Data.Binary as B
import Data.Binary hiding (get, put)
import Foreign.Storable (sizeOf)

import Util.Pretty hiding (Str)

data Option = TTypeInTType
            | CheckConv
  deriving Eq

-- | Source location. These are typically produced by the parser 'Idris.Parser.getFC'
data FC = FC { fc_fname :: String, -- ^ Filename
               fc_line :: Int, -- ^ Line number
               fc_column :: Int -- ^ Column number
             }

-- | Ignore source location equality (so deriving classes do not compare FCs)
instance Eq FC where
  _ == _ = True

-- | FC with equality
newtype FC' = FC' { unwrapFC :: FC }

instance Eq FC' where
  FC' fc == FC' fc' = fcEq fc fc'
    where fcEq (FC n l c) (FC n' l' c') = n == n' && l == l' && c == c'

-- | Empty source location
emptyFC :: FC
emptyFC = fileFC ""

-- | Source location with file only
fileFC :: String -> FC
fileFC s = FC s 0 0

{-!
deriving instance Binary FC
deriving instance NFData FC
!-}

instance Sized FC where
  size (FC f l c) = 1 + length f

instance Show FC where
    show (FC f l c) = f ++ ":" ++ show l ++ ":" ++ show c

-- | Used for error reflection
data ErrorReportPart = TextPart String
                     | NamePart Name
                     | TermPart Term
                     | SubReport [ErrorReportPart]
                       deriving (Show, Eq)


-- Please remember to keep Err synchronised with
-- Language.Reflection.Errors.Err in the stdlib!

-- | Idris errors. Used as exceptions in the compiler, but reported to users
-- if they reach the top level.
data Err = Msg String
          | InternalMsg String
          | CantUnify Bool Term Term Err [(Name, Type)] Int
               -- Int is 'score' - how much we did unify
               -- Bool indicates recoverability, True indicates more info may make
               -- unification succeed
          | InfiniteUnify Name Term [(Name, Type)]
          | CantConvert Term Term [(Name, Type)]
          | CantSolveGoal Term [(Name, Type)]
          | UnifyScope Name Name Term [(Name, Type)]
          | CantInferType String
          | NonFunctionType Term Term
          | NotEquality Term Term
          | TooManyArguments Name
          | CantIntroduce Term
          | NoSuchVariable Name
          | NoTypeDecl Name
          | NotInjective Term Term Term
          | CantResolve Term
          | CantResolveAlts [String]
          | IncompleteTerm Term
          | UniverseError
          | ProgramLineComment
          | Inaccessible Name
          | NonCollapsiblePostulate Name
          | AlreadyDefined Name
          | ProofSearchFail Err
          | NoRewriting Term
          | At FC Err
          | Elaborating String Name Err
          | ProviderError String
          | LoadingFailed String Err
          | ReflectionError [[ErrorReportPart]] Err
          | ReflectionFailed String Err
  deriving Eq
{-!
deriving instance NFData Err
!-}

instance Sized Err where
  size (Msg msg) = length msg
  size (InternalMsg msg) = length msg
  size (CantUnify _ left right err _ score) = size left + size right + size err
  size (InfiniteUnify _ right _) = size right
  size (CantConvert left right _) = size left + size right
  size (UnifyScope _ _ right _) = size right
  size (NoSuchVariable name) = size name
  size (NoTypeDecl name) = size name
  size (NotInjective l c r) = size l + size c + size r
  size (CantResolve trm) = size trm
  size (NoRewriting trm) = size trm
  size (CantResolveAlts _) = 1
  size (IncompleteTerm trm) = size trm
  size UniverseError = 1
  size ProgramLineComment = 1
  size (At fc err) = size fc + size err
  size (Elaborating _ n err) = size err
  size (ProviderError msg) = length msg
  size (LoadingFailed fn e) = 1 + length fn + size e
  size _ = 1

score :: Err -> Int
score (CantUnify _ _ _ m _ s) = s + score m
score (CantResolve _) = 20
score (NoSuchVariable _) = 1000
score (ProofSearchFail _) = 10000
score (CantSolveGoal _ _) = 10000
score (InternalMsg _) = -1
score _ = 0

instance Show Err where
    show (Msg s) = s
    show (InternalMsg s) = "Internal error: " ++ show s
    show (CantUnify _ l r e sc i) = "CantUnify " ++ show l ++ " " ++ show r ++ " "
                                      ++ show e ++ " in " ++ show sc ++ " " ++ show i
    show (CantSolveGoal g _) = "CantSolve " ++ show g
    show (Inaccessible n) = show n ++ " is not an accessible pattern variable"
    show (ProviderError msg) = "Type provider error: " ++ msg
    show (LoadingFailed fn e) = "Loading " ++ fn ++ " failed: (TT) " ++ show e
    show ProgramLineComment = "Program line next to comment"
    show (At f e) = show f ++ ":" ++ show e
    show _ = "Error"

instance Pretty Err where
  pretty (Msg m) = text m
  pretty (CantUnify _ l r e _ i) =
    if size l + size r > breakingSize then
      text "Cannot unify" <+> colon $$
        nest nestingSize (pretty l <+> text "and" <+> pretty r) $$
        nest nestingSize (text "where" <+> pretty e <+> text "with" <+> (text . show $ i))
    else
      text "Cannot unify" <+> colon <+> pretty l <+> text "and" <+> pretty r $$
        nest nestingSize (text "where" <+> pretty e <+> text "with" <+> (text . show $ i))
  pretty (ProviderError msg) = text msg
  pretty err@(LoadingFailed _ _) = text (show err)
  pretty _ = text "Error"

instance Error Err where
  strMsg = InternalMsg

type TC = TC' Err

instance (Pretty a) => Pretty (TC a) where
  pretty (OK ok) = pretty ok
  pretty (Error err) =
    if size err > breakingSize then
      text "Error" <+> colon $$ (nest nestingSize $ pretty err)
    else
      text "Error" <+> colon <+> pretty err

instance Show a => Show (TC a) where
    show (OK x) = show x
    show (Error str) = "Error: " ++ show str

tfail :: Err -> TC a
tfail e = Error e

failMsg :: String -> TC a
failMsg str = Error (Msg str)

trun :: FC -> TC a -> TC a
trun fc (OK a)    = OK a
trun fc (Error e) = Error (At fc e)

discard :: Monad m => m a -> m ()
discard f = f >> return ()

showSep :: String -> [String] -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x:xs) = x ++ sep ++ showSep sep xs

pmap f (x, y) = (f x, f y)

traceWhen True msg a = trace msg a
traceWhen False _  a = a

-- RAW TERMS ----------------------------------------------------------------

-- | Names are hierarchies of strings, describing scope (so no danger of
-- duplicate names, but need to be careful on lookup).
data Name = UN T.Text -- ^ User-provided name
          | NS Name [T.Text] -- ^ Root, namespaces
          | MN Int T.Text -- ^ Machine chosen names
          | NErased -- ^ Name of somethng which is never used in scope
          | SN SpecialName -- ^ Decorated function names
          | SymRef Int -- ^ Reference to IBC file symbol table (used during serialisation)
  deriving (Eq, Ord)

txt :: String -> T.Text
txt = T.pack

str :: T.Text -> String
str = T.unpack

tnull :: T.Text -> Bool
tnull = T.null

thead :: T.Text -> Char
thead = T.head

-- Smart constructors for names, using old String style
sUN :: String -> Name
sUN s = UN (txt s)

sNS :: Name -> [String] -> Name
sNS n ss = NS n (map txt ss)

sMN :: Int -> String -> Name
sMN i s = MN i (txt s)

{-!
deriving instance Binary Name
deriving instance NFData Name
!-}

data SpecialName = WhereN Int Name Name
                 | InstanceN Name [T.Text]
                 | ParentN Name T.Text
                 | MethodN Name
                 | CaseN Name
                 | ElimN Name
  deriving (Eq, Ord)
{-!
deriving instance Binary SpecialName
deriving instance NFData SpecialName
!-}

sInstanceN :: Name -> [String] -> SpecialName
sInstanceN n ss = InstanceN n (map T.pack ss)

sParentN :: Name -> String -> SpecialName
sParentN n s = ParentN n (T.pack s)

instance Sized Name where
  size (UN n)     = 1
  size (NS n els) = 1 + length els
  size (MN i n) = 1
  size _ = 1

instance Pretty Name where
  pretty (UN n) = text (T.unpack n)
  pretty (NS n s) = pretty n
  pretty (MN i s) = lbrace <+> text (T.unpack s) <+> (text . show $ i) <+> rbrace
  pretty (SN s) = text (show s)

instance Show Name where
    show (UN n) = str n
    show (NS n s) = showSep "." (map T.unpack (reverse s)) ++ "." ++ show n
    show (MN _ u) | u == txt "underscore" = "_"
    show (MN i s) = "{" ++ str s ++ show i ++ "}"
    show (SN s) = show s
    show NErased = "_"

instance Show SpecialName where
    show (WhereN i p c) = show p ++ ", " ++ show c
    show (InstanceN cl inst) = showSep ", " (map T.unpack inst) ++ " instance of " ++ show cl
    show (MethodN m) = "method " ++ show m
    show (ParentN p c) = show p ++ "#" ++ T.unpack c
    show (CaseN n) = "case block in " ++ show n
    show (ElimN n) = "<<" ++ show n ++ " eliminator>>"

-- Show a name in a way decorated for code generation, not human reading
showCG :: Name -> String
showCG (UN n) = T.unpack n
showCG (NS n s) = showSep "." (map T.unpack (reverse s)) ++ "." ++ showCG n
showCG (MN _ u) | u == txt "underscore" = "_"
showCG (MN i s) = "{" ++ T.unpack s ++ show i ++ "}"
showCG (SN s) = showCG' s
  where showCG' (WhereN i p c) = showCG p ++ ":" ++ showCG c ++ ":" ++ show i
        showCG' (InstanceN cl inst) = '@':showCG cl ++ '$':showSep ":" (map T.unpack inst)
        showCG' (MethodN m) = '!':showCG m
        showCG' (ParentN p c) = showCG p ++ "#" ++ show c
        showCG' (CaseN c) = showCG c ++ "_case"
        showCG' (ElimN sn) = showCG sn ++ "_elim"
showCG NErased = "_"


-- |Contexts allow us to map names to things. A root name maps to a collection
-- of things in different namespaces with that name.
type Ctxt a = Map.Map Name (Map.Map Name a)
emptyContext = Map.empty

mapCtxt :: (a -> b) -> Ctxt a -> Ctxt b
mapCtxt = fmap . fmap

-- |Return True if the argument 'Name' should be interpreted as the name of a
-- typeclass.
tcname (UN xs) | T.null xs = False
               | otherwise = T.head xs == '@'
tcname (NS n _) = tcname n
tcname (SN (InstanceN _ _)) = True
tcname (SN (MethodN _)) = True
tcname (SN (ParentN _ _)) = True
tcname _ = False

implicitable (NS n _) = implicitable n
implicitable (UN xs) | T.null xs = False
                     | otherwise = isLower (T.head xs)
implicitable (MN _ _) = True
implicitable _ = False

nsroot (NS n _) = n
nsroot n = n

addDef :: Name -> a -> Ctxt a -> Ctxt a
addDef n v ctxt = case Map.lookup (nsroot n) ctxt of
                        Nothing -> Map.insert (nsroot n)
                                        (Map.insert n v Map.empty) ctxt
                        Just xs -> Map.insert (nsroot n)
                                        (Map.insert n v xs) ctxt

{-| Look up a name in the context, given an optional namespace.
   The name (n) may itself have a (partial) namespace given.

   Rules for resolution:

    - if an explicit namespace is given, return the names which match it. If none
      match, return all names.

    - if the name has has explicit namespace given, return the names which match it
      and ignore the given namespace.

    - otherwise, return all names.

-}

lookupCtxtName :: Name -> Ctxt a -> [(Name, a)]
lookupCtxtName n ctxt = case Map.lookup (nsroot n) ctxt of
                                  Just xs -> filterNS (Map.toList xs)
                                  Nothing -> []
  where
    filterNS [] = []
    filterNS ((found, v) : xs)
        | nsmatch n found = (found, v) : filterNS xs
        | otherwise       = filterNS xs

    nsmatch (NS n ns) (NS p ps) = ns `isPrefixOf` ps
    nsmatch (NS _ _)  _         = False
    nsmatch looking   found     = True

lookupCtxt :: Name -> Ctxt a -> [a]
lookupCtxt n ctxt = map snd (lookupCtxtName n ctxt)

lookupCtxtExact :: Name -> Ctxt a -> [a]
lookupCtxtExact n ctxt = [ v | (nm, v) <- lookupCtxtName n ctxt, nm == n]

updateDef :: Name -> (a -> a) -> Ctxt a -> Ctxt a
updateDef n f ctxt
  = let ds = lookupCtxtName n ctxt in
        foldr (\ (n, t) c -> addDef n (f t) c) ctxt ds

toAlist :: Ctxt a -> [(Name, a)]
toAlist ctxt = let allns = map snd (Map.toList ctxt) in
                concat (map (Map.toList) allns)

addAlist :: Show a => [(Name, a)] -> Ctxt a -> Ctxt a
addAlist [] ctxt = ctxt
addAlist ((n, tm) : ds) ctxt = addDef n tm (addAlist ds ctxt)

data NativeTy = IT8 | IT16 | IT32 | IT64
    deriving (Show, Eq, Ord, Enum)

instance Pretty NativeTy where
    pretty IT8  = text "Bits8"
    pretty IT16 = text "Bits16"
    pretty IT32 = text "Bits32"
    pretty IT64 = text "Bits64"

data IntTy = ITFixed NativeTy | ITNative | ITBig | ITChar
           | ITVec NativeTy Int
    deriving (Show, Eq, Ord)

data ArithTy = ATInt IntTy | ATFloat -- TODO: Float vectors
    deriving (Show, Eq, Ord)
{-!
deriving instance NFData IntTy
deriving instance NFData NativeTy
deriving instance NFData ArithTy
!-}

instance Pretty ArithTy where
    pretty (ATInt ITNative) = text "Int"
    pretty (ATInt ITBig) = text "BigInt"
    pretty (ATInt ITChar) = text "Char"
    pretty (ATInt (ITFixed n)) = pretty n
    pretty (ATInt (ITVec e c)) = pretty e <> text "x" <> (text . show $ c)
    pretty ATFloat = text "Float"

nativeTyWidth :: NativeTy -> Int
nativeTyWidth IT8 = 8
nativeTyWidth IT16 = 16
nativeTyWidth IT32 = 32
nativeTyWidth IT64 = 64

{-# DEPRECATED intTyWidth "Non-total function, use nativeTyWidth and appropriate casing" #-}
intTyWidth :: IntTy -> Int
intTyWidth (ITFixed n) = nativeTyWidth n
intTyWidth ITNative = 8 * sizeOf (0 :: Int)
intTyWidth ITChar = error "IRTS.Lang.intTyWidth: Characters have platform and backend dependent width"
intTyWidth ITBig = error "IRTS.Lang.intTyWidth: Big integers have variable width"

data Const = I Int | BI Integer | Fl Double | Ch Char | Str String
           | B8 Word8 | B16 Word16 | B32 Word32 | B64 Word64
           | B8V (Vector Word8) | B16V (Vector Word16)
           | B32V (Vector Word32) | B64V (Vector Word64)
           | AType ArithTy | StrType
           | PtrType | VoidType | Forgot
  deriving (Eq, Ord)
{-!
deriving instance Binary Const
deriving instance NFData Const
!-}

instance Sized Const where
  size _ = 1

instance Pretty Const where
  pretty (I i) = text . show $ i
  pretty (BI i) = text . show $ i
  pretty (Fl f) = text . show $ f
  pretty (Ch c) = text . show $ c
  pretty (Str s) = text s
  pretty (AType a) = pretty a
  pretty StrType = text "String"
  pretty PtrType = text "Ptr"
  pretty VoidType = text "Void"
  pretty Forgot = text "Forgot"
  pretty (B8 w) = text . show $ w
  pretty (B16 w) = text . show $ w
  pretty (B32 w) = text . show $ w
  pretty (B64 w) = text . show $ w

data Raw = Var Name
         | RBind Name (Binder Raw) Raw
         | RApp Raw Raw
         | RType
         | RForce Raw
         | RConstant Const
  deriving (Show, Eq)

instance Sized Raw where
  size (Var name) = 1
  size (RBind name bind right) = 1 + size bind + size right
  size (RApp left right) = 1 + size left + size right
  size RType = 1
  size (RForce raw) = 1 + size raw
  size (RConstant const) = size const

instance Pretty Raw where
  pretty = text . show

{-!
deriving instance Binary Raw
deriving instance NFData Raw
!-}

-- The type parameter `b` will normally be something like `TT Name` or just
-- `Raw`. We do not make a type-level distinction between TT terms that happen
-- to be TT types and TT terms that are not TT types.
-- | All binding forms are represented in a uniform fashion. This type only represents
-- the types of bindings (and their values, if any); the attached identifiers are part
-- of the 'Bind' constructor for the 'TT' type.
data Binder b = Lam   { binderTy  :: !b {-^ type annotation for bound variable-}}
              | Pi    { binderTy  :: !b }
                {-^ A binding that occurs in a function type expression, e.g. @(x:Int) -> ...@ -}
              | Let   { binderTy  :: !b,
                        binderVal :: b {-^ value for bound variable-}}
                -- ^ A binding that occurs in a @let@ expression
              | NLet  { binderTy  :: !b,
                        binderVal :: b }
              | Hole  { binderTy  :: !b}
              | GHole { envlen :: Int,
                        binderTy  :: !b}
              | Guess { binderTy  :: !b,
                        binderVal :: b }
              | PVar  { binderTy  :: !b }
                -- ^ A pattern variable
              | PVTy  { binderTy  :: !b }
  deriving (Show, Eq, Ord, Functor)
{-!
deriving instance Binary Binder
deriving instance NFData Binder
!-}

instance Sized a => Sized (Binder a) where
  size (Lam ty) = 1 + size ty
  size (Pi ty) = 1 + size ty
  size (Let ty val) = 1 + size ty + size val
  size (NLet ty val) = 1 + size ty + size val
  size (Hole ty) = 1 + size ty
  size (GHole _ ty) = 1 + size ty
  size (Guess ty val) = 1 + size ty + size val
  size (PVar ty) = 1 + size ty
  size (PVTy ty) = 1 + size ty

fmapMB :: Monad m => (a -> m b) -> Binder a -> m (Binder b)
fmapMB f (Let t v)   = liftM2 Let (f t) (f v)
fmapMB f (NLet t v)  = liftM2 NLet (f t) (f v)
fmapMB f (Guess t v) = liftM2 Guess (f t) (f v)
fmapMB f (Lam t)     = liftM Lam (f t)
fmapMB f (Pi t)      = liftM Pi (f t)
fmapMB f (Hole t)    = liftM Hole (f t)
fmapMB f (GHole i t)   = liftM (GHole i) (f t)
fmapMB f (PVar t)    = liftM PVar (f t)
fmapMB f (PVTy t)    = liftM PVTy (f t)

raw_apply :: Raw -> [Raw] -> Raw
raw_apply f [] = f
raw_apply f (a : as) = raw_apply (RApp f a) as

raw_unapply :: Raw -> (Raw, [Raw])
raw_unapply t = ua [] t where
    ua args (RApp f a) = ua (a:args) f
    ua args t          = (t, args)

-- WELL TYPED TERMS ---------------------------------------------------------

-- | Universe expressions for universe checking
data UExp = UVar Int -- ^ universe variable
          | UVal Int -- ^ explicit universe level
  deriving (Eq, Ord)
{-!
deriving instance NFData UExp
!-}

instance Sized UExp where
  size _ = 1

-- We assume that universe levels have been checked, so anything external
-- can just have the same universe variable and we won't get any new
-- cycles.

instance Binary UExp where
    put x = return ()
    get = return (UVar (-1))

instance Show UExp where
    show (UVar x) | x < 26 = [toEnum (x + fromEnum 'a')]
                  | otherwise = toEnum ((x `mod` 26) + fromEnum 'a') : show (x `div` 26)
    show (UVal x) = show x
--     show (UMax l r) = "max(" ++ show l ++ ", " ++ show r ++")"

-- | Universe constraints
data UConstraint = ULT UExp UExp -- ^ Strictly less than
                 | ULE UExp UExp -- ^ Less than or equal to
  deriving Eq

instance Show UConstraint where
    show (ULT x y) = show x ++ " < " ++ show y
    show (ULE x y) = show x ++ " <= " ++ show y

type UCs = (Int, [UConstraint])

data NameType = Bound
              | Ref
              | DCon {nt_tag :: Int, nt_arity :: Int} -- ^ Data constructor
              | TCon {nt_tag :: Int, nt_arity :: Int} -- ^ Type constructor
  deriving (Show, Ord)
{-!
deriving instance Binary NameType
deriving instance NFData NameType
!-}

instance Sized NameType where
  size _ = 1

instance Pretty NameType where
  pretty = text . show

instance Eq NameType where
    Bound    == Bound    = True
    Ref      == Ref      = True
    DCon _ a == DCon _ b = (a == b) -- ignore tag
    TCon _ a == TCon _ b = (a == b) -- ignore tag
    _        == _        = False

-- | Terms in the core language. The type parameter is the type of
-- identifiers used for bindings and explicit named references;
-- usually we use @TT 'Name'@.
data TT n = P NameType n (TT n) -- ^ named references with type
            -- (P for "Parameter", motivated by McKinna and Pollack's
            -- Pure Type Systems Formalized)
          | V !Int -- ^ a resolved de Bruijn-indexed variable
          | Bind n !(Binder (TT n)) (TT n) -- ^ a binding
          | App !(TT n) (TT n) -- ^ function, function type, arg
          | Constant Const -- ^ constant
          | Proj (TT n) !Int -- ^ argument projection; runtime only
                             -- (-1) is a special case for 'subtract one from BI'
          | Erased -- ^ an erased term
          | Impossible -- ^ special case for totality checking
          | TType UExp -- ^ the type of types at some level
  deriving (Ord, Functor)
{-!
deriving instance Binary TT
deriving instance NFData TT
!-}

class TermSize a where
  termsize :: Name -> a -> Int

instance TermSize a => TermSize [a] where
    termsize n [] = 0
    termsize n (x : xs) = termsize n x + termsize n xs

instance TermSize (TT Name) where
    termsize n (P _ n' _)
       | n' == n = 1000000 -- recursive => really big
       | otherwise = 1
    termsize n (V _) = 1
    -- for `Bind` terms, we can erroneously declare a term
    -- "recursive => really big" if the name of the bound 
    -- variable is the same as the name we're using
    -- So generate a different name in that case.
    termsize n (Bind n' (Let t v) sc)
       = let rn = if n == n' then sMN 0 "noname" else n in
             termsize rn v + termsize rn sc
    termsize n (Bind n' b sc)
       = let rn = if n == n' then sMN 0 "noname" else n in
             termsize rn sc
    termsize n (App f a) = termsize n f + termsize n a
    termsize n (Proj t i) = termsize n t
    termsize n _ = 1

instance Sized a => Sized (TT a) where
  size (P name n trm) = 1 + size name + size n + size trm
  size (V v) = 1
  size (Bind nm binder bdy) = 1 + size nm + size binder + size bdy
  size (App l r) = 1 + size l + size r
  size (Constant c) = size c
  size Erased = 1
  size (TType u) = 1 + size u

instance Pretty a => Pretty (TT a) where
  pretty _ = text "test"

type EnvTT n = [(n, Binder (TT n))]

data Datatype n = Data { d_typename :: n,
                         d_typetag  :: Int,
                         d_type     :: (TT n),
                         d_cons     :: [(n, TT n)] }
  deriving (Show, Functor, Eq)

instance Eq n => Eq (TT n) where
    (==) (P xt x _)     (P yt y _)     = x == y
    (==) (V x)          (V y)          = x == y
    (==) (Bind _ xb xs) (Bind _ yb ys) = xs == ys && xb == yb
    (==) (App fx ax)    (App fy ay)    = ax == ay && fx == fy
    (==) (TType _)        (TType _)        = True -- deal with constraints later
    (==) (Constant x)   (Constant y)   = x == y
    (==) (Proj x i)     (Proj y j)     = x == y && i == j
    (==) Erased         _              = True
    (==) _              Erased         = True
    (==) _              _              = False

-- * A few handy operations on well typed terms:

-- | A term is injective iff it is a data constructor, type constructor,
-- constant, the type Type, pi-binding, or an application of an injective
-- term.
isInjective :: TT n -> Bool
isInjective (P (DCon _ _) _ _) = True
isInjective (P (TCon _ _) _ _) = True
isInjective (Constant _)       = True
isInjective (TType x)            = True
isInjective (Bind _ (Pi _) sc) = True
isInjective (App f a)          = isInjective f
isInjective _                  = False

-- | Count the number of instances of a de Bruijn index in a term
vinstances :: Int -> TT n -> Int
vinstances i (V x) | i == x = 1
vinstances i (App f a) = vinstances i f + vinstances i a
vinstances i (Bind x b sc) = instancesB b + vinstances (i + 1) sc
  where instancesB (Let t v) = vinstances i v
        instancesB _ = 0
vinstances i t = 0

-- | Replace the outermost (index 0) de Bruijn variable with the given term
instantiate :: TT n -> TT n -> TT n
instantiate e = subst 0 where
    subst i (V x) | i == x = e
    subst i (Bind x b sc) = Bind x (fmap (subst i) b) (subst (i+1) sc)
    subst i (App f a) = App (subst i f) (subst i a)
    subst i (Proj x idx) = Proj (subst i x) idx
    subst i t = t

-- | As 'instantiate', but also decrement the indices of all de Bruijn variables
-- remaining in the term, so that there are no more references to the variable
-- that has been substituted.
substV :: TT n -> TT n -> TT n
substV x tm = dropV 0 (instantiate x tm) where
    dropV i (V x) | x > i = V (x - 1)
                  | otherwise = V x
    dropV i (Bind x b sc) = Bind x (fmap (dropV i) b) (dropV (i+1) sc)
    dropV i (App f a) = App (dropV i f) (dropV i a)
    dropV i (Proj x idx) = Proj (dropV i x) idx
    dropV i t = t

-- | Replace all non-free de Bruijn references in the given term with references
-- to the name of their binding.
explicitNames :: TT n -> TT n
explicitNames (Bind x b sc) = let b' = fmap explicitNames b in
                                  Bind x b'
                                     (explicitNames (instantiate
                                        (P Bound x (binderTy b')) sc))
explicitNames (App f a) = App (explicitNames f) (explicitNames a)
explicitNames (Proj x idx) = Proj (explicitNames x) idx
explicitNames t = t

-- | Replace references to the given 'Name'-like id with references to
-- de Bruijn index 0.
pToV :: Eq n => n -> TT n -> TT n
pToV n = pToV' n 0
pToV' n i (P _ x _) | n == x = V i
pToV' n i (Bind x b sc)
-- We can assume the inner scope has been pToVed already, so continue to
-- resolve names from the *outer* scope which may happen to have the same id.
     | n == x    = Bind x (fmap (pToV' n i) b) sc
     | otherwise = Bind x (fmap (pToV' n i) b) (pToV' n (i+1) sc)
pToV' n i (App f a) = App (pToV' n i f) (pToV' n i a)
pToV' n i (Proj t idx) = Proj (pToV' n i t) idx
pToV' n i t = t

-- increase de Bruijn indices, as if a binder has been added
addBinder :: TT n -> TT n
addBinder t = ab 0 t
  where
     ab top (V i) | i >= top = V (i + 1)
                  | otherwise = V i
     ab top (Bind x b sc) = Bind x (fmap (ab top) b) (ab (top + 1) sc)
     ab top (App f a) = App (ab top f) (ab top a)
     ab top (Proj t idx) = Proj (ab top t) idx
     ab top t = t

-- | Convert several names. First in the list comes out as V 0
pToVs :: Eq n => [n] -> TT n -> TT n
pToVs ns tm = pToVs' ns tm 0 where
    pToVs' []     tm i = tm
    pToVs' (n:ns) tm i = pToV' n i (pToVs' ns tm (i+1))

-- | Replace de Bruijn indices in the given term with explicit references to
-- the names of the bindings they refer to. It is an error if the given term
-- contains free de Bruijn indices.
vToP :: TT n -> TT n
vToP = vToP' [] where
    vToP' env (V i) = let (n, b) = (env !! i) in
                          P Bound n (binderTy b)
    vToP' env (Bind n b sc) = let b' = fmap (vToP' env) b in
                                  Bind n b' (vToP' ((n, b'):env) sc)
    vToP' env (App f a) = App (vToP' env f) (vToP' env a)
    vToP' env t = t

-- | Replace every non-free reference to the name of a binding in
-- the given term with a de Bruijn index.
finalise :: Eq n => TT n -> TT n
finalise (Bind x b sc) = Bind x (fmap finalise b) (pToV x (finalise sc))
finalise (App f a) = App (finalise f) (finalise a)
finalise t = t

-- Once we've finished checking everything about a term we no longer need
-- the type on the 'P' so erase it so save memory

pEraseType :: TT n -> TT n
pEraseType (P nt t _) = P nt t Erased
pEraseType (App f a) = App (pEraseType f) (pEraseType a)
pEraseType (Bind n b sc) = Bind n (fmap pEraseType b) (pEraseType sc)
pEraseType t = t

-- | As 'instantiate', but in addition to replacing @'V' 0@,
-- replace references to the given 'Name'-like id.
subst :: Eq n => n {-^ The id to replace -} ->
         TT n {-^ The replacement term -} ->
         TT n {-^ The term to replace in -} ->
         TT n
subst n v tm = instantiate v (pToV n tm)

-- If there are no Vs in the term (i.e. in proof state)
psubst :: Eq n => n -> TT n -> TT n -> TT n
psubst n v tm = s' tm where
   s' (P _ x _) | n == x = v
   s' (Bind x b sc) | n == x = Bind x (fmap s' b) sc
                    | otherwise = Bind x (fmap s' b) (s' sc)
   s' (App f a) = App (s' f) (s' a)
   s' (Proj t idx) = Proj (s' t) idx
   s' t = t

-- | As 'subst', but takes a list of (name, substitution) pairs instead
-- of a single name and substitution
substNames :: Eq n => [(n, TT n)] -> TT n -> TT n
substNames []             t = t
substNames ((n, tm) : xs) t = subst n tm (substNames xs t)

-- | Replaces all terms equal (in the sense of @(==)@) to
-- the old term with the new term.
substTerm :: Eq n => TT n {-^ Old term -} ->
             TT n {-^ New term -} ->
             TT n {-^ template term -}
             -> TT n
substTerm old new = st where
  st t | t == old = new
  st (App f a) = App (st f) (st a)
  st (Bind x b sc) = Bind x (fmap st b) (st sc)
  st t = t

-- | Returns true if V 0 and bound name n do not occur in the term
noOccurrence :: Eq n => n -> TT n -> Bool
noOccurrence n t = no' 0 t
  where
    no' i (V x) = not (i == x)
    no' i (P Bound x _) = not (n == x)
    no' i (Bind n b sc) = noB' i b && no' (i+1) sc
       where noB' i (Let t v) = no' i t && no' i v
             noB' i (Guess t v) = no' i t && no' i v
             noB' i b = no' i (binderTy b)
    no' i (App f a) = no' i f && no' i a
    no' i (Proj x _) = no' i x
    no' i _ = True

-- | Returns all names used free in the term
freeNames :: Eq n => TT n -> [n]
freeNames (P _ n _) = [n]
freeNames (Bind n (Let t v) sc) = nub $ freeNames v ++ (freeNames sc \\ [n])
                                        ++ freeNames t
freeNames (Bind n b sc) = nub $ freeNames (binderTy b) ++ (freeNames sc \\ [n])
freeNames (App f a) = nub $ freeNames f ++ freeNames a
freeNames (Proj x i) = nub $ freeNames x
freeNames _ = []

-- | Return the arity of a (normalised) type
arity :: TT n -> Int
arity (Bind n (Pi t) sc) = 1 + arity sc
arity _ = 0

-- | Deconstruct an application; returns the function and a list of arguments
unApply :: TT n -> (TT n, [TT n])
unApply t = ua [] t where
    ua args (App f a) = ua (a:args) f
    ua args t         = (t, args)

-- | Returns a term representing the application of the first argument
-- (a function) to every element of the second argument.
mkApp :: TT n -> [TT n] -> TT n
mkApp f [] = f
mkApp f (a:as) = mkApp (App f a) as

unList :: Term -> Maybe [Term]
unList tm = case unApply tm of
              (nil, [_]) -> Just []
              (cons, ([_, x, xs])) ->
                  do rest <- unList xs
                     return $ x:rest
              (f, args) -> Nothing

-- | Cast a 'TT' term to a 'Raw' value, discarding universe information and
-- the types of named references and replacing all de Bruijn indices
-- with the corresponding name. It is an error if there are free de
-- Bruijn indices.
forget :: TT Name -> Raw
forget tm = fe [] tm
  where
    fe env (P _ n _) = Var n
    fe env (V i)     = Var (env !! i)
    fe env (Bind n b sc) = let n' = uniqueName n env in
                               RBind n' (fmap (fe env) b)
                                        (fe (n':env) sc)
    fe env (App f a) = RApp (fe env f) (fe env a)
    fe env (Constant c)
                     = RConstant c
    fe env (TType i)   = RType
    fe env Erased    = RConstant Forgot

-- | Introduce a 'Bind' into the given term for each element of the
-- given list of (name, binder) pairs.
bindAll :: [(n, Binder (TT n))] -> TT n -> TT n
bindAll [] t = t
bindAll ((n, b) : bs) t = Bind n b (bindAll bs t)

-- | Like 'bindAll', but the 'Binder's are 'TT' terms instead.
-- The first argument is a function to map @TT@ terms to @Binder@s.
-- This function might often be something like 'Lam', which directly
-- constructs a @Binder@ from a @TT@ term.
bindTyArgs :: (TT n -> Binder (TT n)) -> [(n, TT n)] -> TT n -> TT n
bindTyArgs b xs = bindAll (map (\ (n, ty) -> (n, b ty)) xs)

-- | Return a list of pairs of the names of the outermost 'Pi'-bound
-- variables in the given term, together with their types.
getArgTys :: TT n -> [(n, TT n)]
getArgTys (Bind n (Pi t) sc) = (n, t) : getArgTys sc
getArgTys _ = []

getRetTy :: TT n -> TT n
getRetTy (Bind n (PVar _) sc) = getRetTy sc
getRetTy (Bind n (PVTy _) sc) = getRetTy sc
getRetTy (Bind n (Pi _) sc)   = getRetTy sc
getRetTy sc = sc

uniqueNameFrom :: [Name] -> [Name] -> Name
uniqueNameFrom (s : supply) hs
       | s `elem` hs = uniqueNameFrom supply hs
       | otherwise   = s

uniqueName :: Name -> [Name] -> Name
uniqueName n hs | n `elem` hs = uniqueName (nextName n) hs
                | otherwise   = n

uniqueBinders :: [Name] -> TT Name -> TT Name
uniqueBinders ns (Bind n b sc)
    = let n' = uniqueName n ns in
          Bind n' (fmap (uniqueBinders (n':ns)) b) (uniqueBinders ns sc)
uniqueBinders ns (App f a) = App (uniqueBinders ns f) (uniqueBinders ns a)
uniqueBinders ns t = t


nextName (NS x s)    = NS (nextName x) s
nextName (MN i n)    = MN (i+1) n
nextName (UN x) = let (num', nm') = T.span isDigit (T.reverse x)
                      nm = T.reverse nm'
                      num = readN (T.reverse num') in
                          UN (nm `T.append` txt (show (num+1)))
  where
    readN x | not (T.null x) = read (T.unpack x)
    readN x = 0
nextName (SN x) = SN (nextName' x)
  where
    nextName' (WhereN i f x) = WhereN i f (nextName x)
    nextName' (CaseN n) = CaseN (nextName n)
    nextName' (MethodN n) = MethodN (nextName n)

type Term = TT Name
type Type = Term

type Env  = EnvTT Name

-- | an environment with de Bruijn indices 'normalised' so that they all refer to
-- this environment

newtype WkEnvTT n = Wk (EnvTT n)
type WkEnv = WkEnvTT Name

instance (Eq n, Show n) => Show (TT n) where
    show t = showEnv [] t

itBitsName IT8 = "Bits8"
itBitsName IT16 = "Bits16"
itBitsName IT32 = "Bits32"
itBitsName IT64 = "Bits64"

instance Show Const where
    show (I i) = show i
    show (BI i) = show i
    show (Fl f) = show f
    show (Ch c) = show c
    show (Str s) = show s
    show (B8 x) = show x
    show (B16 x) = show x
    show (B32 x) = show x
    show (B64 x) = show x
    show (B8V x) = "<" ++ intercalate "," (map show (V.toList x)) ++ ">"
    show (B16V x) = "<" ++ intercalate "," (map show (V.toList x)) ++ ">"
    show (B32V x) = "<" ++ intercalate "," (map show (V.toList x)) ++ ">"
    show (B64V x) = "<" ++ intercalate "," (map show (V.toList x)) ++ ">"
    show (AType ATFloat) = "Float"
    show (AType (ATInt ITBig)) = "Integer"
    show (AType (ATInt ITNative)) = "Int"
    show (AType (ATInt ITChar)) = "Char"
    show (AType (ATInt (ITFixed it))) = itBitsName it
    show (AType (ATInt (ITVec it c))) = itBitsName it ++ "x" ++ show c
    show StrType = "String"
    show PtrType = "Ptr"
    show VoidType = "Void"

showEnv :: (Eq n, Show n) => EnvTT n -> TT n -> String
showEnv env t = showEnv' env t False
showEnvDbg env t = showEnv' env t True

prettyEnv env t = prettyEnv' env t False
  where
    prettyEnv' env t dbg = prettySe 10 env t dbg

    bracket outer inner p
      | inner > outer = lparen <> p <> rparen
      | otherwise     = p

    prettySe p env (P nt n t) debug =
      pretty n <+>
        if debug then
          lbrack <+> pretty nt <+> colon <+> prettySe 10 env t debug <+> rbrack
        else
          empty
    prettySe p env (V i) debug
      | i < length env =
        if debug then
          text . show . fst $ env!!i
        else
          lbrack <+> text (show i) <+> rbrack
      | otherwise      = text "unbound" <+> text (show i) <+> text "!"
    prettySe p env (Bind n b@(Pi t) sc) debug
      | noOccurrence n sc && not debug =
          bracket p 2 $ prettySb env n b debug <> prettySe 10 ((n, b):env) sc debug
    prettySe p env (Bind n b sc) debug =
      bracket p 2 $ prettySb env n b debug <> prettySe 10 ((n, b):env) sc debug
    prettySe p env (App f a) debug =
      bracket p 1 $ prettySe 1 env f debug <+> prettySe 0 env a debug
    prettySe p env (Proj x i) debug =
      prettySe 1 env x debug <+> text ("!" ++ show i)
    prettySe p env (Constant c) debug = pretty c
    prettySe p env Erased debug = text "[_]"
    prettySe p env (TType i) debug = text "Type" <+> (text . show $ i)

    -- Render a `Binder` and its name
    prettySb env n (Lam t) = prettyB env "λ" "=>" n t
    prettySb env n (Hole t) = prettyB env "?defer" "." n t
    prettySb env n (Pi t) = prettyB env "(" ") ->" n t
    prettySb env n (PVar t) = prettyB env "pat" "." n t
    prettySb env n (PVTy t) = prettyB env "pty" "." n t
    prettySb env n (Let t v) = prettyBv env "let" "in" n t v
    prettySb env n (Guess t v) = prettyBv env "??" "in" n t v

    -- Use `op` and `sc` to delimit `n` (a binding name) and its type
    -- declaration
    -- e.g. "λx : Int =>" for the Lam case
    prettyB env op sc n t debug =
      text op <> pretty n <+> colon <+> prettySe 10 env t debug <> text sc

    -- Like `prettyB`, but handle the bindings that have values in addition
    -- to names and types
    prettyBv env op sc n t v debug =
      text op <> pretty n <+> colon <+> prettySe 10 env t debug <+> text "=" <+>
        prettySe 10 env v debug <> text sc


showEnv' env t dbg = se 10 env t where
    se p env (P nt n t) = show n
                            ++ if dbg then "{" ++ show nt ++ " : " ++ se 10 env t ++ "}" else ""
    se p env (V i) | i < length env && i >= 0
                                    = (show $ fst $ env!!i) ++
                                      if dbg then "{" ++ show i ++ "}" else ""
                   | otherwise = "!!V " ++ show i ++ "!!"
    se p env (Bind n b@(Pi t) sc)
        | noOccurrence n sc && not dbg = bracket p 2 $ se 1 env t ++ " -> " ++ se 10 ((n,b):env) sc
    se p env (Bind n b sc) = bracket p 2 $ sb env n b ++ se 10 ((n,b):env) sc
    se p env (App f a) = bracket p 1 $ se 1 env f ++ " " ++ se 0 env a
    se p env (Proj x i) = se 1 env x ++ "!" ++ show i
    se p env (Constant c) = show c
    se p env Erased = "[__]"
    se p env Impossible = "[impossible]"
    se p env (TType i) = "Type " ++ show i

    sb env n (Lam t)  = showb env "\\ " " => " n t
    sb env n (Hole t) = showb env "? " ". " n t
    sb env n (GHole i t) = showb env "?defer " ". " n t
    sb env n (Pi t)   = showb env "(" ") -> " n t
    sb env n (PVar t) = showb env "pat " ". " n t
    sb env n (PVTy t) = showb env "pty " ". " n t
    sb env n (Let t v)   = showbv env "let " " in " n t v
    sb env n (Guess t v) = showbv env "?? " " in " n t v

    showb env op sc n t    = op ++ show n ++ " : " ++ se 10 env t ++ sc
    showbv env op sc n t v = op ++ show n ++ " : " ++ se 10 env t ++ " = " ++
                             se 10 env v ++ sc

    bracket outer inner str | inner > outer = "(" ++ str ++ ")"
                            | otherwise = str

-- | Check whether a term has any holes in it - impure if so
pureTerm :: TT Name -> Bool
pureTerm (App f a) = pureTerm f && pureTerm a
pureTerm (Bind n b sc) = notClassName n && pureBinder b && pureTerm sc where
    pureBinder (Hole _) = False
    pureBinder (Guess _ _) = False
    pureBinder (Let t v) = pureTerm t && pureTerm v
    pureBinder t = pureTerm (binderTy t)

    notClassName (MN _ c) | c == txt "class" = False
    notClassName _ = True

pureTerm _ = True

-- | Weaken a term by adding i to each de Bruijn index (i.e. lift it over i bindings)
weakenTm :: Int -> TT n -> TT n
weakenTm i t = wk i 0 t
  where wk i min (V x) | x >= min = V (i + x)
        wk i m (App f a)     = App (wk i m f) (wk i m a)
        wk i m (Bind x b sc) = Bind x (wkb i m b) (wk i (m + 1) sc)
        wk i m t = t
        wkb i m t           = fmap (wk i m) t

-- | Weaken an environment so that all the de Bruijn indices are correct according
-- to the latest bound variable

weakenEnv :: EnvTT n -> EnvTT n
weakenEnv env = wk (length env - 1) env
  where wk i [] = []
        wk i ((n, b) : bs) = (n, weakenTmB i b) : wk (i - 1) bs
        weakenTmB i (Let   t v) = Let (weakenTm i t) (weakenTm i v)
        weakenTmB i (Guess t v) = Guess (weakenTm i t) (weakenTm i v)
        weakenTmB i t           = t { binderTy = weakenTm i (binderTy t) }

-- | Weaken every term in the environment by the given amount
weakenTmEnv :: Int -> EnvTT n -> EnvTT n
weakenTmEnv i = map (\ (n, b) -> (n, fmap (weakenTm i) b))

-- | Gather up all the outer 'PVar's and 'Hole's in an expression and reintroduce
-- them in a canonical order
orderPats :: Term -> Term
orderPats tm = op [] tm
  where
    op ps (Bind n (PVar t) sc) = op ((n, PVar t) : ps) sc
    op ps (Bind n (Hole t) sc) = op ((n, Hole t) : ps) sc
    op ps sc = bindAll (sortP ps) sc

    sortP ps = pick [] (reverse ps)

    namesIn (P _ n _) = [n]
    namesIn (Bind n b t) = nub $ nb b ++ (namesIn t \\ [n])
      where nb (Let   t v) = nub (namesIn t) ++ nub (namesIn v)
            nb (Guess t v) = nub (namesIn t) ++ nub (namesIn v)
            nb t = namesIn (binderTy t)
    namesIn (App f a) = nub (namesIn f ++ namesIn a)
    namesIn _ = []

    pick acc [] = reverse acc
    pick acc ((n, t) : ps) = pick (insert n t acc) ps

    insert n t [] = [(n, t)]
    insert n t ((n',t') : ps)
        | n `elem` (namesIn (binderTy t') ++
                      concatMap namesIn (map (binderTy . snd) ps))
            = (n', t') : insert n t ps
        | otherwise = (n,t):(n',t'):ps


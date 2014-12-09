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
import Numeric (showIntAtBase)
import qualified Data.Text as T
import Data.List hiding (insert)
import Data.Set(Set, member, fromList, insert)
import Data.Maybe (listToMaybe)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
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
               fc_start :: (Int, Int), -- ^ Line and column numbers for the start of the location span
               fc_end :: (Int, Int) -- ^ Line and column numbers for the end of the location span
             }

-- | Ignore source location equality (so deriving classes do not compare FCs)
instance Eq FC where
  _ == _ = True

-- | FC with equality
newtype FC' = FC' { unwrapFC :: FC }

instance Eq FC' where
  FC' fc == FC' fc' = fcEq fc fc'
    where fcEq (FC n s e) (FC n' s' e') = n == n' && s == s' && e == e'

-- | Empty source location
emptyFC :: FC
emptyFC = fileFC ""

-- | Source location with file only
fileFC :: String -> FC
fileFC s = FC s (0, 0) (0, 0)

{-!
deriving instance Binary FC
deriving instance NFData FC
!-}

instance Sized FC where
  size (FC f s e) = 4 + length f

instance Show FC where
    show (FC f s e) = f ++ ":" ++ showLC s e
      where showLC (sl, sc) (el, ec) | sl == el && sc == ec = show sl ++ ":" ++ show sc
                                     | sl == el             = show sl ++ ":" ++ show sc ++ "-" ++ show ec
                                     | otherwise            = show sl ++ ":" ++ show sc ++ "-" ++ show el ++ ":" ++ show ec

-- | Output annotation for pretty-printed name - decides colour
data NameOutput = TypeOutput | FunOutput | DataOutput | MetavarOutput | PostulateOutput

-- | Text formatting output
data TextFormatting = BoldText | ItalicText | UnderlineText

-- | Output annotations for pretty-printing
data OutputAnnotation = AnnName Name (Maybe NameOutput) (Maybe String) (Maybe String)
                        -- ^^ The name, classification, docs overview, and pretty-printed type
                      | AnnBoundName Name Bool
                        -- ^^ The name and whether it is implicit
                      | AnnConst Const
                      | AnnData String String -- ^ type, doc overview
                      | AnnType String String -- ^ name, doc overview
                      | AnnKeyword
                      | AnnFC FC
                      | AnnTextFmt TextFormatting
                      | AnnTerm [(Name, Bool)] (TT Name) -- ^ pprint bound vars, original term
                      | AnnSearchResult Ordering -- ^ more general, isomorphic, or more specific
                      | AnnErr Err

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
data Err' t
          = Msg String
          | InternalMsg String
          | CantUnify Bool t t (Err' t) [(Name, t)] Int
               -- Int is 'score' - how much we did unify
               -- Bool indicates recoverability, True indicates more info may make
               -- unification succeed
          | InfiniteUnify Name t [(Name, t)]
          | CantConvert t t [(Name, t)]
          | CantSolveGoal t [(Name, t)]
          | UnifyScope Name Name t [(Name, t)]
          | CantInferType String
          | NonFunctionType t t
          | NotEquality t t
          | TooManyArguments Name
          | CantIntroduce t
          | NoSuchVariable Name
          | WithFnType t
          | NoTypeDecl Name
          | NotInjective t t t
          | CantResolve t
          | CantResolveAlts [Name]
          | IncompleteTerm t
          | UniverseError
          | UniqueError Universe Name
          | UniqueKindError Universe Name
          | ProgramLineComment
          | Inaccessible Name
          | NonCollapsiblePostulate Name
          | AlreadyDefined Name
          | ProofSearchFail (Err' t)
          | NoRewriting t
          | At FC (Err' t)
          | Elaborating String Name (Err' t)
          | ElaboratingArg Name Name [(Name, Name)] (Err' t)
          | ProviderError String
          | LoadingFailed String (Err' t)
          | ReflectionError [[ErrorReportPart]] (Err' t)
          | ReflectionFailed String (Err' t)
  deriving (Eq, Functor)

type Err = Err' Term

{-!
deriving instance NFData Err
!-}

instance Sized ErrorReportPart where
  size (TextPart msg) = 1 + length msg
  size (TermPart t) = 1 + size t
  size (NamePart n) = 1 + size n
  size (SubReport rs) = 1 + size rs

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
  size (ElaboratingArg _ _ _ err) = size err
  size (ProviderError msg) = length msg
  size (LoadingFailed fn e) = 1 + length fn + size e
  size _ = 1

score :: Err -> Int
score (CantUnify _ _ _ m _ s) = s + score m
score (CantResolve _) = 20
score (NoSuchVariable _) = 1000
score (ProofSearchFail e) = score e
score (CantSolveGoal _ _) = 100000
score (InternalMsg _) = -1
score (At _ e) = score e
score (ElaboratingArg _ _ _ e) = score e
score (Elaborating _ _ e) = score e
score _ = 0

instance Show Err where
    show (Msg s) = s
    show (InternalMsg s) = "Internal error: " ++ show s
    show (CantUnify rec l r e sc i) = "CantUnify " ++ show rec ++ " " ++
                                         show l ++ " " ++ show r ++ " " ++
                                         show e ++ " in " ++ show sc ++ " " ++ show i
    show (CantSolveGoal g _) = "CantSolve " ++ show g
    show (Inaccessible n) = show n ++ " is not an accessible pattern variable"
    show (ProviderError msg) = "Type provider error: " ++ msg
    show (LoadingFailed fn e) = "Loading " ++ fn ++ " failed: (TT) " ++ show e
    show ProgramLineComment = "Program line next to comment"
    show (At f e) = show f ++ ":" ++ show e
    show (ElaboratingArg f x prev e) = "Elaborating " ++ show f ++ " arg " ++
                                       show x ++ ": " ++ show e
    show (Elaborating what n e) = "Elaborating " ++ what ++ show n ++ ":" ++ show e
    show (ProofSearchFail e) = "Proof search fail: " ++ show e
    show _ = "Error"

instance Pretty Err OutputAnnotation where
  pretty (Msg m) = text m
  pretty (CantUnify _ l r e _ i) =
      text "Cannot unify" <+> colon <+> pretty l <+> text "and" <+> pretty r <+>
      nest nestingSize (text "where" <+> pretty e <+> text "with" <+> (text . show $ i))
  pretty (ProviderError msg) = text msg
  pretty err@(LoadingFailed _ _) = text (show err)
  pretty _ = text "Error"

instance Error Err where
  strMsg = InternalMsg

type TC = TC' Err

instance (Pretty a OutputAnnotation) => Pretty (TC a) OutputAnnotation where
  pretty (OK ok) = pretty ok
  pretty (Error err) =
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
          | NErased -- ^ Name of something which is never used in scope
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
                 | WithN Int Name
                 | InstanceN Name [T.Text]
                 | ParentN Name T.Text
                 | MethodN Name
                 | CaseN Name
                 | ElimN Name
                 | InstanceCtorN Name
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

instance Pretty Name OutputAnnotation where
  pretty n@(UN n') = annotate (AnnName n Nothing Nothing Nothing) $ text (T.unpack n')
  pretty n@(NS un s) = annotate (AnnName n Nothing Nothing Nothing) . noAnnotate $ pretty un
  pretty n@(MN i s) = annotate (AnnName n Nothing Nothing Nothing) $
                      lbrace <+> text (T.unpack s) <+> (text . show $ i) <+> rbrace
  pretty n@(SN s) = annotate (AnnName n Nothing Nothing Nothing) $ text (show s)

instance Pretty [Name] OutputAnnotation where
  pretty = encloseSep empty empty comma . map pretty

instance Show Name where
    show (UN n) = str n
    show (NS n s) = showSep "." (map T.unpack (reverse s)) ++ "." ++ show n
    show (MN _ u) | u == txt "underscore" = "_"
    show (MN i s) = "{" ++ str s ++ show i ++ "}"
    show (SN s) = show s
    show NErased = "_"

instance Show SpecialName where
    show (WhereN i p c) = show p ++ ", " ++ show c
    show (WithN i n) = "with block in " ++ show n
    show (InstanceN cl inst) = showSep ", " (map T.unpack inst) ++ " instance of " ++ show cl
    show (MethodN m) = "method " ++ show m
    show (ParentN p c) = show p ++ "#" ++ T.unpack c
    show (CaseN n) = "case block in " ++ show n
    show (ElimN n) = "<<" ++ show n ++ " eliminator>>"
    show (InstanceCtorN n) = "constructor of " ++ show n

-- Show a name in a way decorated for code generation, not human reading
showCG :: Name -> String
showCG (UN n) = T.unpack n
showCG (NS n s) = showSep "." (map T.unpack (reverse s)) ++ "." ++ showCG n
showCG (MN _ u) | u == txt "underscore" = "_"
showCG (MN i s) = "{" ++ T.unpack s ++ show i ++ "}"
showCG (SN s) = showCG' s
  where showCG' (WhereN i p c) = showCG p ++ ":" ++ showCG c ++ ":" ++ show i
        showCG' (WithN i n) = "_" ++ showCG n ++ "_with_" ++ show i
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
                     | otherwise = isLower (T.head xs) || T.head xs == '_'
implicitable (MN _ x) = not (tnull x) && thead x /= '_'
implicitable _ = False

nsroot (NS n _) = n
nsroot n = n

-- this will overwrite already existing definitions
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

lookupCtxtExact :: Name -> Ctxt a -> Maybe a
lookupCtxtExact n ctxt = listToMaybe [ v | (nm, v) <- lookupCtxtName n ctxt, nm == n]

deleteDefExact :: Name -> Ctxt a -> Ctxt a
deleteDefExact n = Map.adjust (Map.delete n) (nsroot n)

updateDef :: Name -> (a -> a) -> Ctxt a -> Ctxt a
updateDef n f ctxt
  = let ds = lookupCtxtName n ctxt in
        foldr (\ (n, t) c -> addDef n (f t) c) ctxt ds

toAlist :: Ctxt a -> [(Name, a)]
toAlist ctxt = let allns = map snd (Map.toList ctxt) in
                concatMap (Map.toList) allns

addAlist :: Show a => [(Name, a)] -> Ctxt a -> Ctxt a
addAlist [] ctxt = ctxt
addAlist ((n, tm) : ds) ctxt = addDef n tm (addAlist ds ctxt)

data NativeTy = IT8 | IT16 | IT32 | IT64
    deriving (Show, Eq, Ord, Enum)

instance Pretty NativeTy OutputAnnotation where
    pretty IT8  = text "Bits8"
    pretty IT16 = text "Bits16"
    pretty IT32 = text "Bits32"
    pretty IT64 = text "Bits64"

data IntTy = ITFixed NativeTy | ITNative | ITBig | ITChar
           | ITVec NativeTy Int
    deriving (Show, Eq, Ord)

intTyName :: IntTy -> String
intTyName ITNative = "Int"
intTyName ITBig = "BigInt"
intTyName (ITFixed sized) = "B" ++ show (nativeTyWidth sized)
intTyName (ITChar) = "Char"
intTyName (ITVec ity count) = "B" ++ show (nativeTyWidth ity) ++ "x" ++ show count

data ArithTy = ATInt IntTy | ATFloat -- TODO: Float vectors https://github.com/idris-lang/Idris-dev/issues/1723
    deriving (Show, Eq, Ord)
{-!
deriving instance NFData IntTy
deriving instance NFData NativeTy
deriving instance NFData ArithTy
!-}

instance Pretty ArithTy OutputAnnotation where
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
           | PtrType | ManagedPtrType | BufferType | VoidType | Forgot
  deriving (Eq, Ord)
{-!
deriving instance Binary Const
deriving instance NFData Const
!-}

instance Sized Const where
  size _ = 1

instance Pretty Const OutputAnnotation where
  pretty (I i) = text . show $ i
  pretty (BI i) = text . show $ i
  pretty (Fl f) = text . show $ f
  pretty (Ch c) = text . show $ c
  pretty (Str s) = text s
  pretty (AType a) = pretty a
  pretty StrType = text "String"
  pretty BufferType = text "prim__UnsafeBuffer"
  pretty PtrType = text "Ptr"
  pretty ManagedPtrType = text "Ptr"
  pretty VoidType = text "Void"
  pretty Forgot = text "Forgot"
  pretty (B8 w) = text . show $ w
  pretty (B16 w) = text . show $ w
  pretty (B32 w) = text . show $ w
  pretty (B64 w) = text . show $ w

-- | Determines whether the input constant represents a type
constIsType :: Const -> Bool
constIsType (I _) = False
constIsType (BI _) = False
constIsType (Fl _) = False
constIsType (Ch _) = False
constIsType (Str _) = False
constIsType (B8 _) = False
constIsType (B16 _) = False
constIsType (B32 _) = False
constIsType (B64 _) = False
constIsType (B8V _) = False
constIsType (B16V _) = False
constIsType (B32V _) = False
constIsType (B64V _) = False
constIsType _ = True

-- | Get the docstring for a Const
constDocs :: Const -> String
constDocs c@(AType (ATInt ITBig))          = "Arbitrary-precision integers"
constDocs c@(AType (ATInt ITNative))       = "Fixed-precision integers of undefined size"
constDocs c@(AType (ATInt ITChar))         = "Characters in some unspecified encoding"
constDocs c@(AType ATFloat)                = "Double-precision floating-point numbers"
constDocs StrType                          = "Strings in some unspecified encoding"
constDocs PtrType                          = "Foreign pointers"
constDocs ManagedPtrType                   = "Managed pointers"
constDocs BufferType                       = "Copy-on-write buffers"
constDocs c@(AType (ATInt (ITFixed IT8)))  = "Eight bits (unsigned)"
constDocs c@(AType (ATInt (ITFixed IT16))) = "Sixteen bits (unsigned)"
constDocs c@(AType (ATInt (ITFixed IT32))) = "Thirty-two bits (unsigned)"
constDocs c@(AType (ATInt (ITFixed IT64))) = "Sixty-four bits (unsigned)"
constDocs c@(AType (ATInt (ITVec IT8 16))) = "Vectors of sixteen eight-bit values"
constDocs c@(AType (ATInt (ITVec IT16 8))) = "Vectors of eight sixteen-bit values"
constDocs c@(AType (ATInt (ITVec IT32 4))) = "Vectors of four thirty-two-bit values"
constDocs c@(AType (ATInt (ITVec IT64 2))) = "Vectors of two sixty-four-bit values"
constDocs (Fl f)                           = "A float"
constDocs (I i)                            = "A fixed-precision integer"
constDocs (BI i)                           = "An arbitrary-precision integer"
constDocs (Str s)                          = "A string of length " ++ show (length s)
constDocs (Ch c)                           = "A character"
constDocs (B8 w)                           = "The eight-bit value 0x" ++
                                             showIntAtBase 16 intToDigit w ""
constDocs (B16 w)                          = "The sixteen-bit value 0x" ++
                                             showIntAtBase 16 intToDigit w ""
constDocs (B32 w)                          = "The thirty-two-bit value 0x" ++
                                             showIntAtBase 16 intToDigit w ""
constDocs (B64 w)                          = "The sixty-four-bit value 0x" ++
                                             showIntAtBase 16 intToDigit w ""
constDocs (B8V v)                          = "A vector of eight-bit values"
constDocs (B16V v)                         = "A vector of sixteen-bit values"
constDocs (B32V v)                         = "A vector of thirty-two-bit values"
constDocs (B64V v)                         = "A vector of sixty-four-bit values"
constDocs prim                             = "Undocumented"

data Universe = NullType | UniqueType | AllTypes
  deriving (Eq, Ord)

instance Show Universe where
    show UniqueType = "UniqueType"
    show NullType = "NullType"
    show AllTypes = "Type*"

data Raw = Var Name
         | RBind Name (Binder Raw) Raw
         | RApp Raw Raw
         | RType
         | RUType Universe
         | RForce Raw
         | RConstant Const
  deriving (Show, Eq)

instance Sized Raw where
  size (Var name) = 1
  size (RBind name bind right) = 1 + size bind + size right
  size (RApp left right) = 1 + size left + size right
  size RType = 1
  size (RUType _) = 1
  size (RForce raw) = 1 + size raw
  size (RConstant const) = size const

instance Pretty Raw OutputAnnotation where
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
              | Pi    { binderTy  :: !b,
                        binderKind :: !b }
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
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
{-!
deriving instance Binary Binder
deriving instance NFData Binder
!-}

instance Sized a => Sized (Binder a) where
  size (Lam ty) = 1 + size ty
  size (Pi ty _) = 1 + size ty
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
fmapMB f (Pi t k)    = liftM2 Pi (f t) (f k)
fmapMB f (Hole t)    = liftM Hole (f t)
fmapMB f (GHole i t) = liftM (GHole i) (f t)
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
              | DCon {nt_tag :: Int, nt_arity :: Int, nt_unique :: Bool} -- ^ Data constructor
              | TCon {nt_tag :: Int, nt_arity :: Int} -- ^ Type constructor
  deriving (Show, Ord)
{-!
deriving instance Binary NameType
deriving instance NFData NameType
!-}

instance Sized NameType where
  size _ = 1

instance Pretty NameType OutputAnnotation where
  pretty = text . show

instance Eq NameType where
    Bound    == Bound    = True
    Ref      == Ref      = True
    DCon _ a _ == DCon _ b _ = (a == b) -- ignore tag
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
          | UType Universe -- ^ Uniqueness type universe (disjoint from TType)
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

instance Pretty a o => Pretty (TT a) o where
  pretty _ = text "test"

type EnvTT n = [(n, Binder (TT n))]

data Datatype n = Data { d_typename :: n,
                         d_typetag  :: Int,
                         d_type     :: (TT n),
                         d_unique   :: Bool,
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
isInjective (P (DCon _ _ _) _ _) = True
isInjective (P (TCon _ _) _ _) = True
isInjective (Constant _)       = True
isInjective (TType x)            = True
isInjective (Bind _ (Pi _ _) sc) = True
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
-- subst n v tm = instantiate v (pToV n tm)
subst n v tm = fst $ subst' 0 tm
  where
    -- keep track of updates to save allocations - this is a big win on
    -- large terms in particular
    -- ('Maybe' would be neater here, but >>= is not the right combinator.
    -- Feel free to tidy up, as long as it still saves allocating when no
    -- substitution happens...)
    subst' i (V x) | i == x = (v, True)
    subst' i (P _ x _) | n == x = (v, True)
    subst' i t@(Bind x b sc) | x /= n
         = let (b', ub) = substB' i b
               (sc', usc) = subst' (i+1) sc in
               if ub || usc then (Bind x b' sc', True) else (t, False)
    subst' i t@(App f a) = let (f', uf) = subst' i f
                               (a', ua) = subst' i a in
                               if uf || ua then (App f' a', True) else (t, False)
    subst' i t@(Proj x idx) = let (x', u) = subst' i x in
                                  if u then (Proj x' idx, u) else (t, False)
    subst' i t = (t, False)

    substB' i b@(Let t v) = let (t', ut) = subst' i t
                                (v', uv) = subst' i v in
                                if ut || uv then (Let t' v', True)
                                            else (b, False)
    substB' i b@(Guess t v) = let (t', ut) = subst' i t
                                  (v', uv) = subst' i v in
                                  if ut || uv then (Guess t' v', True)
                                              else (b, False)
    substB' i b = let (ty', u) = subst' i (binderTy b) in
                      if u then (b { binderTy = ty' }, u) else (b, False)

-- If there are no Vs in the term (i.e. in proof state)
psubst :: Eq n => n -> TT n -> TT n -> TT n
psubst n v tm = s' 0 tm where
   s' i (V x) | x > i = V (x - 1)
              | x == i = v
              | otherwise = V x
   s' i (P _ x _) | n == x = v
   s' i (Bind x b sc) | n == x = Bind x (fmap (s' i) b) sc
                      | otherwise = Bind x (fmap (s' i) b) (s' (i+1) sc)
   s' i (App f a) = App (s' i f) (s' i a)
   s' i (Proj t idx) = Proj (s' i t) idx
   s' i t = t

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

-- | Return number of occurrences of V 0 or bound name i the term
occurrences :: Eq n => n -> TT n -> Int
occurrences n t = execState (no' 0 t) 0
  where
    no' i (V x) | i == x = do num <- get; put (num + 1)
    no' i (P Bound x _) | n == x = do num <- get; put (num + 1)
    no' i (Bind n b sc) = do noB' i b; no' (i+1) sc
       where noB' i (Let t v) = do no' i t; no' i v
             noB' i (Guess t v) = do no' i t; no' i v
             noB' i b = no' i (binderTy b)
    no' i (App f a) = do no' i f; no' i a
    no' i (Proj x _) = no' i x
    no' i _ = return ()

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
arity (Bind n (Pi t _) sc) = 1 + arity sc
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
forget tm = forgetEnv [] tm

forgetEnv :: [Name] -> TT Name -> Raw
forgetEnv env (P _ n _) = Var n
forgetEnv env (V i)     = Var (env !! i)
forgetEnv env (Bind n b sc) = let n' = uniqueName n env in
                                  RBind n' (fmap (forgetEnv env) b)
                                           (forgetEnv (n':env) sc)
forgetEnv env (App f a) = RApp (forgetEnv env f) (forgetEnv env a)
forgetEnv env (Constant c) = RConstant c
forgetEnv env (TType i) = RType
forgetEnv env (UType u) = RUType u
forgetEnv env Erased    = RConstant Forgot

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
getArgTys (Bind n (PVar _) sc) = getArgTys sc
getArgTys (Bind n (PVTy _) sc) = getArgTys sc
getArgTys (Bind n (Pi t _) sc) = (n, t) : getArgTys sc
getArgTys _ = []

getRetTy :: TT n -> TT n
getRetTy (Bind n (PVar _) sc) = getRetTy sc
getRetTy (Bind n (PVTy _) sc) = getRetTy sc
getRetTy (Bind n (Pi _ _) sc)   = getRetTy sc
getRetTy sc = sc

uniqueNameFrom :: [Name] -> [Name] -> Name
uniqueNameFrom (s : supply) hs
       | s `elem` hs = uniqueNameFrom supply hs
       | otherwise   = s

uniqueName :: Name -> [Name] -> Name
uniqueName n hs | n `elem` hs = uniqueName (nextName n) hs
                | otherwise   = n

uniqueNameSet :: Name -> Set Name -> Name
uniqueNameSet n hs | n `member` hs = uniqueNameSet (nextName n) hs
                | otherwise   = n

uniqueBinders :: [Name] -> TT Name -> TT Name
uniqueBinders ns = ubSet (fromList ns) where
    ubSet ns (Bind n b sc)
        = let n' = uniqueNameSet n ns
              ns' = insert n' ns in
              Bind n' (fmap (ubSet ns') b) (ubSet ns' sc)
    ubSet ns (App f a) = App (ubSet ns f) (ubSet ns a)
    ubSet ns t = t


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
    nextName' (WithN i n) = WithN i (nextName n)
    nextName' (InstanceN n ns) = InstanceN (nextName n) ns
    nextName' (ParentN n ns) = ParentN (nextName n) ns
    nextName' (CaseN n) = CaseN (nextName n)
    nextName' (ElimN n) = ElimN (nextName n)
    nextName' (MethodN n) = MethodN (nextName n)
    nextName' (InstanceCtorN n) = InstanceCtorN (nextName n)

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
    show BufferType = "prim__UnsafeBuffer"
    show PtrType = "Ptr"
    show ManagedPtrType = "ManagedPtr"
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
          lbracket <+> pretty nt <+> colon <+> prettySe 10 env t debug <+> rbracket
        else
          empty
    prettySe p env (V i) debug
      | i < length env =
        if debug then
          text . show . fst $ env!!i
        else
          lbracket <+> text (show i) <+> rbracket
      | otherwise      = text "unbound" <+> text (show i) <+> text "!"
    prettySe p env (Bind n b@(Pi t _) sc) debug
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
    prettySb env n (Pi t _) = prettyB env "(" ") ->" n t
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
    se p env (Bind n b@(Pi t k) sc)
        | noOccurrence n sc && not dbg = bracket p 2 $ se 1 env t ++ arrow k ++ se 10 ((n,b):env) sc
       where arrow (TType _) = " -> "
             arrow u = " [" ++ show u ++ "] -> "
    se p env (Bind n b sc) = bracket p 2 $ sb env n b ++ se 10 ((n,b):env) sc
    se p env (App f a) = bracket p 1 $ se 1 env f ++ " " ++ se 0 env a
    se p env (Proj x i) = se 1 env x ++ "!" ++ show i
    se p env (Constant c) = show c
    se p env Erased = "[__]"
    se p env Impossible = "[impossible]"
    se p env (TType i) = "Type " ++ show i
    se p env (UType u) = show u

    sb env n (Lam t)  = showb env "\\ " " => " n t
    sb env n (Hole t) = showb env "? " ". " n t
    sb env n (GHole i t) = showb env "?defer " ". " n t
    sb env n (Pi t _)   = showb env "(" ") -> " n t
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
    op [] (App f a) = App f (op [] a) -- for Infer terms

    op ps (Bind n (PVar t) sc) = op ((n, PVar t) : ps) sc
    op ps (Bind n (Hole t) sc) = op ((n, Hole t) : ps) sc
    op ps (Bind n (Pi t k) sc) = op ((n, Pi t k) : ps) sc
    op ps sc = bindAll (sortP ps) sc

    sortP ps = pick [] (reverse ps)

    pick acc [] = reverse acc
    pick acc ((n, t) : ps) = pick (insert n t acc) ps

    insert n t [] = [(n, t)]
    insert n t ((n',t') : ps)
        | n `elem` (refsIn (binderTy t') ++
                      concatMap refsIn (map (binderTy . snd) ps))
            = (n', t') : insert n t ps
        | otherwise = (n,t):(n',t'):ps

refsIn :: TT Name -> [Name]
refsIn (P _ n _) = [n]
refsIn (Bind n b t) = nub $ nb b ++ (refsIn t \\ [n])
  where nb (Let   t v) = nub (refsIn t) ++ nub (refsIn v)
        nb (Guess t v) = nub (refsIn t) ++ nub (refsIn v)
        nb t = refsIn (binderTy t)
refsIn (App f a) = nub (refsIn f ++ refsIn a)
refsIn _ = []

-- Make sure all the pattern bindings are as far out as possible
liftPats :: Term -> Term
liftPats tm = let (tm', ps) = runState (getPats tm) [] in
                  orderPats $ bindPats (reverse ps) tm'
  where
    bindPats []          tm = tm
    bindPats ((n, t):ps) tm
         | n `notElem` map fst ps = Bind n (PVar t) (bindPats ps tm)
         | otherwise = bindPats ps tm

    getPats :: Term -> State [(Name, Type)] Term
    getPats (Bind n (PVar t) sc) = do ps <- get
                                      put ((n, t) : ps)
                                      getPats sc
    getPats (Bind n (Guess t v) sc) = do t' <- getPats t
                                         v' <- getPats v
                                         sc' <- getPats sc
                                         return (Bind n (Guess t' v') sc')
    getPats (Bind n (Let t v) sc) = do t' <- getPats t
                                       v' <- getPats v
                                       sc' <- getPats sc
                                       return (Bind n (Let t' v') sc')
    getPats (Bind n (Pi t k) sc) = do t' <- getPats t
                                      k' <- getPats k
                                      sc' <- getPats sc
                                      return (Bind n (Pi t' k') sc')
    getPats (Bind n (Lam t) sc) = do t' <- getPats t
                                     sc' <- getPats sc
                                     return (Bind n (Lam t') sc')
    getPats (Bind n (Hole t) sc) = do t' <- getPats t
                                      sc' <- getPats sc
                                      return (Bind n (Hole t') sc')


    getPats (App f a) = do f' <- getPats f
                           a' <- getPats a
                           return (App f' a')
    getPats t = return t

allTTNames :: Eq n => TT n -> [n]
allTTNames = nub . allNamesIn
  where allNamesIn (P _ n _) = [n]
        allNamesIn (Bind n b t) = [n] ++ nb b ++ allNamesIn t
          where nb (Let   t v) = allNamesIn t ++ allNamesIn v
                nb (Guess t v) = allNamesIn t ++ allNamesIn v
                nb t = allNamesIn (binderTy t)
        allNamesIn (App f a) = allNamesIn f ++ allNamesIn a
        allNamesIn _ = []

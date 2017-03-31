{-|
Module      : Idris.Core.TT
Description : The core language of Idris, TT.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.

TT is the core language of Idris. The language has:

   * Full dependent types

   * A hierarchy of universes, with cumulativity: Type : Type1, Type1 : Type2, ...

   * Pattern matching letrec binding

   * (primitive types defined externally)

   Some technical stuff:

   * Typechecker is kept as simple as possible - no unification, just a checker for incomplete terms.

   * We have a simple collection of tactics which we use to elaborate source
     programs with implicit syntax into fully explicit terms.
-}
{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, DeriveGeneric, FlexibleContexts,
             FunctionalDependencies, MultiParamTypeClasses, PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Idris.Core.TT(
    AppStatus(..), ArithTy(..), Binder(..), Const(..), Ctxt(..)
  , ConstraintFC(..), DataOpt(..), DataOpts(..), Datatype(..)
  , Env(..), EnvTT(..), Err(..), Err'(..), ErrorReportPart(..)
  , FC(..), FC'(..), ImplicitInfo(..), IntTy(..), Name(..)
  , NameOutput(..), NameType(..), NativeTy(..), OutputAnnotation(..)
  , Provenance(..), Raw(..), RigCount(..), SpecialName(..), TC(..), Term(..)
  , TermSize(..), TextFormatting(..), TT(..),Type(..), TypeInfo(..)
  , UConstraint(..), UCs(..), UExp(..), Universe(..)
  , addAlist, addBinder, addDef, allTTNames, arity, bindAll
  , bindingOf, bindTyArgs, caseName, constDocs, constIsType, deleteDefExact
  , discard, emptyContext, emptyFC, explicitNames, fc_end, fc_fname
  , fc_start, fcIn, fileFC, finalise, fmapMB, forget, forgetEnv
  , freeNames, getArgTys, getRetTy, substRetTy, implicitable, instantiate, internalNS
  , intTyName, isInjective, isTypeConst, lookupCtxt
  , lookupCtxtExact, lookupCtxtName, mapCtxt, mkApp, nativeTyWidth
  , nextName, noOccurrence, nsroot, occurrences
  , pEraseType, pmap, pprintRaw, pprintTT, pprintTTClause, prettyEnv, psubst
  , pToV, pToVs, pureTerm, raw_apply, raw_unapply, refsIn, safeForget
  , safeForgetEnv, showCG, showEnv, showEnvDbg, showSep
  , sImplementationN, sMN, sNS, spanFC, str, subst, substNames, substTerm
  , substV, sUN, tcname, termSmallerThan, tfail, thead, tnull
  , toAlist, traceWhen, txt, unApply, uniqueBinders, uniqueName
  , uniqueNameFrom, uniqueNameSet, unList, updateDef, vToP, weakenTm
  , rigPlus, rigMult, fstEnv, rigEnv, sndEnv, lookupBinder, envBinders
  , envZero
  ) where

import Util.Pretty hiding (Str)

-- Work around AMP without CPP
import Prelude (Bool(..), Double, Enum(..), Eq(..), FilePath, Functor(..), Int,
                Integer, Maybe(..), Monad(..), Num(..), Ord(..), Ordering(..),
                Read(..), Show(..), String, div, error, flip, fst, mod, not,
                otherwise, read, snd, ($), (&&), (.), (||))

import Control.Applicative (Alternative, Applicative(..))
import qualified Control.Applicative as A (Alternative(..))
import Control.DeepSeq (($!!))
import Control.Monad.State.Strict
import Control.Monad.Trans.Except (Except(..))
import Data.Binary hiding (get, put)
import qualified Data.Binary as B
import Data.Char
import Data.Data (Data)
import Data.Foldable (Foldable)
import Data.List hiding (group, insert)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import Data.Monoid (mconcat)
import Data.Set (Set, fromList, insert, member)
import qualified Data.Text as T
import Data.Traversable (Traversable)
import Data.Typeable (Typeable)
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as V
import Debug.Trace
import Foreign.Storable (sizeOf)
import GHC.Generics (Generic)
import Numeric (showIntAtBase)
import Numeric.IEEE (IEEE(identicalIEEE))

data Option = TTypeInTType
            | CheckConv
  deriving Eq

-- | Source location. These are typically produced by the parser 'Idris.Parser.getFC'
data FC = FC { _fc_fname :: String, -- ^ Filename
               _fc_start :: (Int, Int), -- ^ Line and column numbers for the start of the location span
               _fc_end :: (Int, Int) -- ^ Line and column numbers for the end of the location span
             }
        | NoFC -- ^ Locations for machine-generated terms
        | FileFC { _fc_fname :: String } -- ^ Locations with file only
  deriving (Data, Generic, Typeable, Ord)

-- TODO: find uses and destroy them, doing this case analysis at call sites
-- | Give a notion of filename associated with an FC
fc_fname :: FC -> String
fc_fname (FC f _ _) = f
fc_fname NoFC = "(no file)"
fc_fname (FileFC f) = f

-- TODO: find uses and destroy them, doing this case analysis at call sites
-- | Give a notion of start location associated with an FC
fc_start :: FC -> (Int, Int)
fc_start (FC _ start _) = start
fc_start NoFC = (0, 0)
fc_start (FileFC f) = (0, 0)

-- TODO: find uses and destroy them, doing this case analysis at call sites
-- | Give a notion of end location associated with an FC
fc_end :: FC -> (Int, Int)
fc_end (FC _ _ end) = end
fc_end NoFC = (0, 0)
fc_end (FileFC f) = (0, 0)

-- | Get the largest span containing the two FCs
spanFC :: FC -> FC -> FC
spanFC (FC f start end) (FC f' start' end')
    | f == f' = FC f (minLocation start start') (maxLocation end end')
    | otherwise = NoFC
  where minLocation (l, c) (l', c') =
          case compare l l' of
            LT -> (l, c)
            EQ -> (l, min c c')
            GT -> (l', c')
        maxLocation (l, c) (l', c') =
          case compare l l' of
            LT -> (l', c')
            EQ -> (l, max c c')
            GT -> (l, c)
spanFC fc@(FC f _ _) (FileFC f') | f == f' = fc
                                 | otherwise = NoFC
spanFC (FileFC f') fc@(FC f _ _) | f == f' = fc
                                 | otherwise = NoFC
spanFC (FileFC f) (FileFC f') | f == f' = FileFC f
                              | otherwise = NoFC
spanFC NoFC fc = fc
spanFC fc NoFC = fc

-- | Determine whether the first argument is completely contained in the second
fcIn :: FC -> FC -> Bool
fcIn NoFC   _ = False
fcIn (FileFC _) _ = False
fcIn (FC {}) NoFC = False
fcIn (FC {}) (FileFC _) = False
fcIn (FC fn1 (sl1, sc1) (el1, ec1)) (FC fn2 (sl2, sc2) (el2, ec2)) =
  fn1 == fn2 &&
  (sl1 == sl2 && sc1 > sc2 || sl1 > sl2) &&
  (el1 == el2 && ec1 < ec2 || el1 < el2)

-- | Ignore source location equality (so deriving classes do not compare FCs)
instance Eq FC where
  _ == _ = True

-- | FC with equality
newtype FC' = FC' { unwrapFC :: FC } deriving (Data, Generic, Typeable, Ord)

instance Eq FC' where
  FC' fc == FC' fc' = fcEq fc fc'
    where fcEq (FC n s e) (FC n' s' e') = n == n' && s == s' && e == e'
          fcEq NoFC NoFC = True
          fcEq (FileFC f) (FileFC f') = f == f'
          fcEq _ _ = False

instance Show FC' where
  showsPrec d (FC' fc) = showsPrec d fc

-- | Empty source location
emptyFC :: FC
emptyFC = NoFC

-- | Source location with file only
fileFC :: String -> FC
fileFC s = FileFC s

{-!
deriving instance Binary FC
!-}

instance Sized FC where
  size (FC f s e) = 4 + length f
  size NoFC = 1
  size (FileFC f) = length f

instance Show FC where
    show (FC f s e) = f ++ ":" ++ showLC s e
      where showLC (sl, sc) (el, ec) | sl == el && sc == ec = show sl ++ ":" ++ show sc
                                     | sl == el             = show sl ++ ":" ++ show sc ++ "-" ++ show ec
                                     | otherwise            = show sl ++ ":" ++ show sc ++ "-" ++ show el ++ ":" ++ show ec
    show NoFC = "No location"
    show (FileFC f) = f

-- | Output annotation for pretty-printed name - decides colour
data NameOutput = TypeOutput | FunOutput | DataOutput | MetavarOutput | PostulateOutput deriving (Show, Eq, Generic)

-- | Text formatting output
data TextFormatting = BoldText | ItalicText | UnderlineText deriving (Show, Eq, Generic)

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
                      | AnnLink String -- ^ A link to this URL
                      | AnnTerm [(Name, Bool)] (TT Name) -- ^ pprint bound vars, original term
                      | AnnSearchResult Ordering -- ^ more general, isomorphic, or more specific
                      | AnnErr Err
                      | AnnNamespace [T.Text] (Maybe FilePath)
                        -- ^ A namespace (e.g. on an import line or in
                        -- a namespace declaration). Stored starting
                        -- at the root, with the hierarchy fully
                        -- resolved. If a file path is present, then
                        -- the namespace represents a module imported
                        -- from that file.
                      | AnnQuasiquote
                      | AnnAntiquote
  deriving (Show, Eq, Generic)

-- | Used for error reflection
data ErrorReportPart = TextPart String
                     | NamePart Name
                     | TermPart Term
                     | RawPart Raw
                     | SubReport [ErrorReportPart]
                       deriving (Show, Eq, Ord, Data, Generic, Typeable)


data Provenance = ExpectedType
                | TooManyArgs Term
                | InferredVal
                | GivenVal
                | SourceTerm Term
  deriving (Show, Eq, Ord, Data, Generic, Typeable)
{-!
deriving instance Binary Err
!-}


-- NB: Please remember to keep Err synchronised with
-- Language.Reflection.Errors.Err in the stdlib!

-- | Idris errors. Used as exceptions in the compiler, but reported to users
-- if they reach the top level.
data Err' t
          = Msg String
          | InternalMsg String
          | CantUnify Bool (t, Maybe Provenance) -- Expected type, provenance
                           (t, Maybe Provenance) -- Actual type, provenance
                           (Err' t) [(Name, t)] Int
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
          | CantResolve Bool -- True if postponed, False if fatal
                        t (Err' t) -- any further information
          | InvalidTCArg Name t
          | CantResolveAlts [Name]
          | NoValidAlts [Name]
          | IncompleteTerm t
          | NoEliminator String t
          | UniverseError FC UExp (Int, Int) (Int, Int) [ConstraintFC]
            -- ^ Location, bad universe, old domain, new domain, suspects
          | UniqueError Universe Name
          | UniqueKindError Universe Name
          | ProgramLineComment
          | Inaccessible Name
          | UnknownImplicit Name Name
          | CantMatch t
          | NonCollapsiblePostulate Name
          | AlreadyDefined Name
          | ProofSearchFail (Err' t)
          | NoRewriting t t t
          | At FC (Err' t)
          | Elaborating String Name (Maybe t) (Err' t)
          | ElaboratingArg Name Name [(Name, Name)] (Err' t)
          | ProviderError String
          | LoadingFailed String (Err' t)
          | ReflectionError [[ErrorReportPart]] (Err' t)
          | ReflectionFailed String (Err' t)
          | ElabScriptDebug [ErrorReportPart] t [(Name, t, [(Name, Binder t)])]
            -- ^ User-specified message, proof term, goals with context (first goal is focused)
          | ElabScriptStuck t
          | RunningElabScript (Err' t) -- ^ The error occurred during a top-level elaboration script
          | ElabScriptStaging Name
          | FancyMsg [ErrorReportPart]
  deriving (Eq, Ord, Functor, Data, Generic, Typeable)

type Err = Err' Term

data TC a = OK !a
          | Error Err
  deriving (Eq, Functor)

bindTC :: TC a -> (a -> TC b) -> TC b
bindTC x k = case x of
                OK v -> k v
                Error e -> Error e
{-# INLINE bindTC #-}

instance Monad TC where
    return x = OK x
    x >>= k = bindTC x k
    fail e = Error (InternalMsg e)

instance MonadPlus TC where
    mzero = fail "Unknown error"
    (OK x) `mplus` _ = OK x
    _ `mplus` (OK y) = OK y
    err `mplus` _    = err


instance Applicative TC where
    pure = return
    (<*>) = ap

instance Alternative TC where
    empty = mzero
    (<|>) = mplus

instance Sized ErrorReportPart where
  size (TextPart msg) = 1 + length msg
  size (TermPart t) = 1 + size t
  size (RawPart r) = 1 + size r
  size (NamePart n) = 1 + size n
  size (SubReport rs) = 1 + size rs

instance Sized Err where
  size (Msg msg) = length msg
  size (InternalMsg msg) = length msg
  size (CantUnify _ left right err _ score) = size (fst left) + size (fst right) + size err
  size (InfiniteUnify _ right _) = size right
  size (CantConvert left right _) = size left + size right
  size (UnifyScope _ _ right _) = size right
  size (NoSuchVariable name) = size name
  size (NoTypeDecl name) = size name
  size (NotInjective l c r) = size l + size c + size r
  size (CantResolve _ trm _) = size trm
  size (NoRewriting l r t) = size l + size r + size t
  size (CantResolveAlts _) = 1
  size (IncompleteTerm trm) = size trm
  size ProgramLineComment = 1
  size (At fc err) = size fc + size err
  size (Elaborating _ _ _ err) = size err
  size (ElaboratingArg _ _ _ err) = size err
  size (ProviderError msg) = length msg
  size (LoadingFailed fn e) = 1 + length fn + size e
  size _ = 1

instance Show Err where
    show (Msg s) = s
    show (InternalMsg s) = "Internal error: " ++ show s
    show (CantUnify rcv l r e sc i) = "CantUnify " ++ show rcv ++ " " ++
                                         show l ++ " and " ++ show r ++ " " ++
                                         show e ++ " in " ++ show sc ++ " " ++ show i
    show (CantConvert l r sc) = "CantConvert " ++
                                         show l ++ " and " ++ show r ++ " " ++
                                         " in " ++ show sc
    show (CantSolveGoal g _) = "CantSolve " ++ show g
    show (Inaccessible n) = show n ++ " is not an accessible pattern variable"
    show (UnknownImplicit n f) = show n ++ " is not an implicit argument of " ++ show f
    show (ProviderError msg) = "Type provider error: " ++ msg
    show (LoadingFailed fn e) = "Loading " ++ fn ++ " failed: (TT) " ++ show e
    show ProgramLineComment = "Program line next to comment"
    show (At f e) = show f ++ ":" ++ show e
    show (ElaboratingArg f x prev e) = "Elaborating " ++ show f ++ " arg " ++
                                       show x ++ ": " ++ show e
    show (Elaborating what n ty e) = "Elaborating " ++ what ++ show n ++
                                     showType ty ++ ":" ++ show e
        where
          showType Nothing = ""
          showType (Just ty) = " with expected type " ++ show ty
    show (ProofSearchFail e) = "Proof search fail: " ++ show e
    show (InfiniteUnify _ _ _) = "InfiniteUnify"
    show (UnifyScope _ _ _ _) = "UnifyScope"
    show (NonFunctionType _ _) = "NonFunctionType"
    show (NotEquality _ _) = "NotEquality"
    show (TooManyArguments _) = "TooManyArguments"
    show (CantIntroduce _) = "CantIntroduce"
    show (NoSuchVariable n) = "NoSuchVariable " ++ show n
    show (WithFnType _) = "WithFnType"
    show (NoTypeDecl _) = "NoTypeDecl"
    show (NotInjective _ _ _) = "NotInjective"
    show (CantResolve _ _ _) = "CantResolve"
    show (InvalidTCArg _ _) = "InvalidTCArg"
    show (CantResolveAlts _) = "CantResolveAlts"
    show (NoValidAlts _) = "NoValidAlts"
    show (IncompleteTerm _) = "IncompleteTerm"
    show _ = "Error"

instance Pretty Err OutputAnnotation where
  pretty (Msg m) = text m
  pretty (CantUnify _ (l, _) (r, _) e _ i) =
      text "Cannot unify" <+> colon <+> pretty l <+> text "and" <+> pretty r <+>
      nest nestingSize (text "where" <+> pretty e <+> text "with" <+> (text . show $ i))
  pretty (ProviderError msg) = text msg
  pretty err@(LoadingFailed _ _) = text (show err)
  pretty _ = text "Error"

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
data Name = UN !T.Text -- ^ User-provided name
          | NS !Name [T.Text] -- ^ Root, namespaces
          | MN !Int !T.Text -- ^ Machine chosen names
          | SN !SpecialName -- ^ Decorated function names
          | SymRef Int -- ^ Reference to IBC file symbol table (used during serialisation)
  deriving (Eq, Ord, Data, Generic, Typeable)

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
sNS n ss = NS n $!! (map txt ss)

sMN :: Int -> String -> Name
sMN i s = MN i (txt s)

caseName (SN (CaseN _ _)) = True
caseName (NS n _) = caseName n
caseName _ = False


{-!
deriving instance Binary Name
!-}

data SpecialName = WhereN !Int !Name !Name
                 | WithN !Int !Name
                 | ImplementationN !Name [T.Text]
                 | ParentN !Name !T.Text
                 | MethodN !Name
                 | CaseN !FC' !Name
                 | ElimN !Name
                 | ImplementationCtorN !Name
                 | MetaN !Name !Name
  deriving (Eq, Ord, Data, Generic, Typeable)
{-!
deriving instance Binary SpecialName
!-}

sImplementationN :: Name -> [String] -> SpecialName
sImplementationN n ss = ImplementationN n (map T.pack ss)

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
  pretty n@(SymRef i) = annotate (AnnName n Nothing Nothing Nothing) $
                        text $ "##symbol" ++ show i ++ "##"

instance Pretty [Name] OutputAnnotation where
  pretty = encloseSep empty empty comma . map pretty

instance Show Name where
    show (UN n) = str n
    show (NS n s) = showSep "." (map T.unpack (reverse s)) ++ "." ++ show n
    show (MN _ u) | u == txt "underscore" = "_"
    show (MN i s) = "{" ++ str s ++ "_" ++ show i ++ "}"
    show (SN s) = show s
    show (SymRef i) = "##symbol" ++ show i ++ "##"

instance Show SpecialName where
    show (WhereN i p c) = show p ++ ", " ++ show c
    show (WithN i n) = "with block in " ++ show n
    show (ImplementationN cl impl) = showSep ", " (map T.unpack impl) ++ " implementation of " ++ show cl
    show (MethodN m) = "method " ++ show m
    show (ParentN p c) = show p ++ "#" ++ T.unpack c
    show (CaseN fc n) = "case block in " ++ show n ++
                        if fc == FC' emptyFC then "" else " at " ++ show fc
    show (ElimN n) = "<<" ++ show n ++ " eliminator>>"
    show (ImplementationCtorN n) = "constructor of " ++ show n
    show (MetaN parent meta) = "<<" ++ show parent ++ " " ++ show meta ++ ">>"

-- Show a name in a way decorated for code generation, not human reading
showCG :: Name -> String
showCG (UN n) = T.unpack n
showCG (NS n s) = showSep "." (map T.unpack (reverse s)) ++ "." ++ showCG n
showCG (MN _ u) | u == txt "underscore" = "_"
showCG (MN i s) = "{" ++ T.unpack s ++ "_" ++ show i ++ "}"
showCG (SN s) = showCG' s
  where showCG' (WhereN i p c) = showCG p ++ ":" ++ showCG c ++ ":" ++ show i
        showCG' (WithN i n) = "_" ++ showCG n ++ "_with_" ++ show i
        showCG' (ImplementationN cl impl) = '@':showCG cl ++ '$':showSep ":" (map T.unpack impl)
        showCG' (MethodN m) = '!':showCG m
        showCG' (ParentN p c) = showCG p ++ "#" ++ show c
        showCG' (CaseN fc c) = showCG c ++ showFC' fc ++ "_case"
        showCG' (ElimN sn) = showCG sn ++ "_elim"
        showCG' (ImplementationCtorN n) = showCG n ++ "_ictor"
        showCG' (MetaN parent meta) = showCG parent ++ "_meta_" ++ showCG meta
        showFC' (FC' NoFC) = ""
        showFC' (FC' (FileFC f)) = "_" ++ cgFN f
        showFC' (FC' (FC f s e))
          | s == e = "_" ++ cgFN f ++
                     "_" ++ show (fst s) ++ "_" ++ show (snd s)
          | otherwise = "_" ++ cgFN f ++
                        "_" ++ show (fst s) ++ "_" ++ show (snd s) ++
                        "_" ++ show (fst e) ++ "_" ++ show (snd e)
        cgFN = concatMap (\c -> if not (isDigit c || isLetter c) then "__" else [c])
showCG (SymRef i) = error "can't do codegen for a symbol reference"


-- |Contexts allow us to map names to things. A root name maps to a collection
-- of things in different namespaces with that name.
type Ctxt a = Map.Map Name (Map.Map Name a)
emptyContext = Map.empty

mapCtxt :: (a -> b) -> Ctxt a -> Ctxt b
mapCtxt = fmap . fmap

-- |Return True if the argument 'Name' should be interpreted as the name of a
-- interface.
tcname (UN xs) = False
tcname (NS n _) = tcname n
tcname (SN (ImplementationN _ _)) = True
tcname (SN (MethodN _)) = True
tcname (SN (ParentN _ _)) = True
tcname _ = False

implicitable (NS n _) = False
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
  = case lookupCtxtExact n ctxt of
         Just t -> addDef n (f t) ctxt
         Nothing -> ctxt

toAlist :: Ctxt a -> [(Name, a)]
toAlist ctxt = let allns = map snd (Map.toList ctxt) in
                concatMap (Map.toList) allns

addAlist :: [(Name, a)] -> Ctxt a -> Ctxt a
addAlist [] ctxt = ctxt
addAlist ((n, tm) : ds) ctxt = addDef n tm (addAlist ds ctxt)

data NativeTy = IT8 | IT16 | IT32 | IT64
    deriving (Show, Eq, Ord, Enum, Data, Generic, Typeable)

instance Pretty NativeTy OutputAnnotation where
    pretty IT8  = text "Bits8"
    pretty IT16 = text "Bits16"
    pretty IT32 = text "Bits32"
    pretty IT64 = text "Bits64"

data IntTy = ITFixed NativeTy | ITNative | ITBig | ITChar
    deriving (Show, Eq, Ord, Data, Generic, Typeable)

intTyName :: IntTy -> String
intTyName ITNative = "Int"
intTyName ITBig = "BigInt"
intTyName (ITFixed sized) = "B" ++ show (nativeTyWidth sized)
intTyName (ITChar) = "Char"

data ArithTy = ATInt IntTy | ATFloat -- TODO: Float vectors https://github.com/idris-lang/Idris-dev/issues/1723
    deriving (Show, Eq, Ord, Data, Generic, Typeable)

instance Pretty ArithTy OutputAnnotation where
    pretty (ATInt ITNative) = text "Int"
    pretty (ATInt ITBig) = text "BigInt"
    pretty (ATInt ITChar) = text "Char"
    pretty (ATInt (ITFixed n)) = pretty n
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
           | AType ArithTy | StrType
           | WorldType | TheWorld
           | VoidType | Forgot
  deriving (Ord, Data, Generic, Typeable)

-- We need to compare Double using bit-pattern identity rather than
-- Haskell's Eq, which equates 0.0 and -0.0, leading to a
-- contradiction in the type theory. Bit-pattern identity will also
-- avoid similar problems for NaNs.
instance Eq Const where
  I i       == I j       = i == j
  BI i      == BI j      = i == j
  Fl i      == Fl j      = identicalIEEE i j
  Ch i      == Ch j      = i == j
  Str i     == Str j     = i == j
  B8 i      == B8 j      = i == j
  B16 i     == B16 j     = i == j
  B32 i     == B32 j     = i == j
  B64 i     == B64 j     = i == j
  AType i   == AType j   = i == j
  StrType   == StrType   = True
  WorldType == WorldType = True
  TheWorld  == TheWorld  = True
  VoidType  == VoidType  = True
  Forgot    == Forgot    = True
  _         == _         = False

{-!
deriving instance Binary Const
!-}

isTypeConst :: Const -> Bool
isTypeConst (AType _) = True
isTypeConst StrType = True
isTypeConst WorldType = True
isTypeConst VoidType = True
isTypeConst _ = False

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
  pretty TheWorld = text "%theWorld"
  pretty WorldType = text "prim__World"
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
constIsType _ = True

-- | Get the docstring for a Const
constDocs :: Const -> String
constDocs c@(AType (ATInt ITBig))          = "Arbitrary-precision integers"
constDocs c@(AType (ATInt ITNative))       = "Fixed-precision integers of undefined size"
constDocs c@(AType (ATInt ITChar))         = "Characters in some unspecified encoding"
constDocs c@(AType ATFloat)                = "Double-precision floating-point numbers"
constDocs StrType                          = "Strings in some unspecified encoding"
constDocs c@(AType (ATInt (ITFixed IT8)))  = "Eight bits (unsigned)"
constDocs c@(AType (ATInt (ITFixed IT16))) = "Sixteen bits (unsigned)"
constDocs c@(AType (ATInt (ITFixed IT32))) = "Thirty-two bits (unsigned)"
constDocs c@(AType (ATInt (ITFixed IT64))) = "Sixty-four bits (unsigned)"
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
constDocs prim                             = "Undocumented"

data Universe = NullType | UniqueType | AllTypes
  deriving (Eq, Ord, Data, Generic, Typeable)

instance Show Universe where
    show UniqueType = "UniqueType"
    show NullType = "NullType"
    show AllTypes = "AnyType"

data Raw = Var Name
         | RBind Name (Binder Raw) Raw
         | RApp Raw Raw
         | RType
         | RUType Universe
         | RConstant Const
  deriving (Show, Eq, Ord, Data, Generic, Typeable)

instance Sized Raw where
  size (Var name) = 1
  size (RBind name bind right) = 1 + size bind + size right
  size (RApp left right) = 1 + size left + size right
  size RType = 1
  size (RUType _) = 1
  size (RConstant const) = size const

instance Pretty Raw OutputAnnotation where
  pretty = text . show

{-!
deriving instance Binary Raw
!-}

data ImplicitInfo = Impl { tcimplementation :: Bool, toplevel_imp :: Bool,
                           machine_gen :: Bool }
  deriving (Show, Eq, Ord, Data, Generic, Typeable)

{-!
deriving instance Binary ImplicitInfo
!-}

-- The type parameter `b` will normally be something like `TT Name` or just
-- `Raw`. We do not make a type-level distinction between TT terms that happen
-- to be TT types and TT terms that are not TT types.
-- | All binding forms are represented in a uniform fashion. This type only represents
-- the types of bindings (and their values, if any); the attached identifiers are part
-- of the 'Bind' constructor for the 'TT' type.
data Binder b = Lam   { binderCount :: RigCount,
                        binderTy  :: !b {-^ type annotation for bound variable-}}
                -- ^ A function binding
              | Pi    { binderCount :: RigCount,
                        binderImpl :: Maybe ImplicitInfo,
                        binderTy  :: !b,
                        binderKind :: !b }
                -- ^ A binding that occurs in a function type
                -- expression, e.g. @(x:Int) -> ...@ The 'binderImpl'
                -- flag says whether it was a scoped implicit
                -- (i.e. forall bound) in the high level Idris, but
                -- otherwise has no relevance in TT.
              | Let   { binderTy  :: !b,
                        binderVal :: b {-^ value for bound variable-}}
                -- ^ A binding that occurs in a @let@ expression
              | NLet  { binderTy  :: !b,
                        binderVal :: b }
                -- ^ NLet is an intermediate product in the evaluator
                -- that's used for temporarily naming locals during
                -- reduction. It won't occur outside the evaluator.
              | Hole  { binderTy  :: !b}
                -- ^ A hole in a term under construction in the
                -- elaborator. If this is not filled during
                -- elaboration, it is an error.
              | GHole { envlen :: Int,
                        localnames :: [Name],
                        binderTy  :: !b}
                -- ^ A saved TT hole that will later be converted to a
                -- top-level Idris metavariable applied to all
                -- elements of its local environment.
              | Guess { binderTy  :: !b,
                        binderVal :: b }
                -- ^ A provided value for a hole. It will later be
                -- substituted - the guess is to keep it
                -- computationally inert while working on other things
                -- if necessary.
              | PVar  { binderCount :: RigCount,
                        binderTy  :: !b }
                -- ^ A pattern variable (these are bound around terms
                -- that make up pattern-match clauses)
              | PVTy  { binderTy  :: !b }
                -- ^ The type of a pattern binding
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Data, Generic, Typeable)
{-!
deriving instance Binary Binder
!-}

instance Sized a => Sized (Binder a) where
  size (Lam _ ty) = 1 + size ty
  size (Pi _ _ ty _) = 1 + size ty
  size (Let ty val) = 1 + size ty + size val
  size (NLet ty val) = 1 + size ty + size val
  size (Hole ty) = 1 + size ty
  size (GHole _ _ ty) = 1 + size ty
  size (Guess ty val) = 1 + size ty + size val
  size (PVar _ ty) = 1 + size ty
  size (PVTy ty) = 1 + size ty

fmapMB :: Monad m => (a -> m b) -> Binder a -> m (Binder b)
fmapMB f (Let t v)   = liftM2 Let (f t) (f v)
fmapMB f (NLet t v)  = liftM2 NLet (f t) (f v)
fmapMB f (Guess t v) = liftM2 Guess (f t) (f v)
fmapMB f (Lam c t)   = liftM (Lam c) (f t)
fmapMB f (Pi c i t k) = liftM2 (Pi c i) (f t) (f k)
fmapMB f (Hole t)    = liftM Hole (f t)
fmapMB f (GHole i ns t) = liftM (GHole i ns) (f t)
fmapMB f (PVar c t)    = liftM (PVar c) (f t)
fmapMB f (PVTy t)    = liftM PVTy (f t)

raw_apply :: Raw -> [Raw] -> Raw
raw_apply f [] = f
raw_apply f (a : as) = raw_apply (RApp f a) as

raw_unapply :: Raw -> (Raw, [Raw])
raw_unapply t = ua [] t where
    ua args (RApp f a) = ua (a:args) f
    ua args t          = (t, args)

-- WELL TYPED TERMS ---------------------------------------------------------

internalNS :: String
internalNS = "(internal)"

-- | Universe expressions for universe checking
data UExp = UVar String Int -- ^ universe variable, with source file to disambiguate
          | UVal Int -- ^ explicit universe level
  deriving (Eq, Ord, Data, Generic, Typeable)

instance Sized UExp where
  size _ = 1

instance Show UExp where
    show (UVar ns x)
       | x < 26 = ns ++ "." ++ [toEnum (x + fromEnum 'a')]
       | otherwise = ns ++ "." ++ toEnum ((x `mod` 26) + fromEnum 'a') : show (x `div` 26)
    show (UVal x) = show x
--     show (UMax l r) = "max(" ++ show l ++ ", " ++ show r ++")"

-- | Universe constraints
data UConstraint = ULT UExp UExp -- ^ Strictly less than
                 | ULE UExp UExp -- ^ Less than or equal to
  deriving (Eq, Ord, Data, Generic, Typeable)

data ConstraintFC = ConstraintFC { uconstraint :: UConstraint,
                                   ufc :: FC }
  deriving (Show, Data, Generic, Typeable)

instance Eq ConstraintFC where
    x == y = uconstraint x == uconstraint y

instance Ord ConstraintFC where
    compare x y = compare (uconstraint x) (uconstraint y)

instance Show UConstraint where
    show (ULT x y) = show x ++ " < " ++ show y
    show (ULE x y) = show x ++ " <= " ++ show y

type UCs = (Int, [UConstraint])

data NameType = Bound
              | Ref
              | DCon {nt_tag :: Int, nt_arity :: Int, nt_unique :: Bool} -- ^ Data constructor
              | TCon {nt_tag :: Int, nt_arity :: Int} -- ^ Type constructor
  deriving (Show, Ord, Data, Generic, Typeable)
{-!
deriving instance Binary NameType
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

data AppStatus n = Complete
                 | MaybeHoles
                 | Holes [n]
    deriving (Eq, Ord, Functor, Data, Generic, Typeable, Show)

-- | Terms in the core language. The type parameter is the type of
-- identifiers used for bindings and explicit named references;
-- usually we use @TT 'Name'@.
data TT n = P NameType n (TT n) -- ^ named references with type
            -- (P for "Parameter", motivated by McKinna and Pollack's
            -- Pure Type Systems Formalized)
          | V !Int -- ^ a resolved de Bruijn-indexed variable
          | Bind n !(Binder (TT n)) (TT n) -- ^ a binding
          | App (AppStatus n) !(TT n) (TT n) -- ^ function, function type, arg
          | Constant Const -- ^ constant
          | Proj (TT n) !Int -- ^ argument projection; runtime only
                             -- (-1) is a special case for 'subtract one from BI'
          | Erased -- ^ an erased term
          | Impossible -- ^ special case for totality checking
          | Inferred (TT n) -- ^ For building case trees when coverage checkimg only.
                            -- Marks a term as being inferred by the machine, rather than
                            -- given by the programmer
          | TType UExp -- ^ the type of types at some level
          | UType Universe -- ^ Uniqueness type universe (disjoint from TType)
  deriving (Ord, Functor, Data, Generic, Typeable)
{-!
deriving instance Binary TT
!-}

class TermSize a where
  termsize :: Name -> a -> Int

instance TermSize a => TermSize [a] where
    termsize n [] = 0
    termsize n (x : xs) = termsize n x + termsize n xs

instance TermSize (TT Name) where
    termsize n (P _ n' _)
       | n' == n = 1000000 -- recursive => really big
       | caseName n' = 1000000 -- case, not safe to inline for termination check
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
    termsize n (App _ f a) = termsize n f + termsize n a
    termsize n (Proj t i) = termsize n t
    termsize n _ = 1

instance Sized Universe where
  size u = 1

instance Sized a => Sized (TT a) where
  size (P name n trm) = 1 + size name + size n + size trm
  size (V v) = 1
  size (Bind nm binder bdy) = 1 + size nm + size binder + size bdy
  size (App _ l r) = 1 + size l + size r
  size (Constant c) = size c
  size Erased = 1
  size (TType u) = 1 + size u
  size (Proj a _) = 1 + size a
  size Impossible = 1
  size (Inferred t) = size t
  size (UType u) = 1 + size u

instance Pretty a o => Pretty (TT a) o where
  pretty _ = text "test"

data RigCount = Rig0 | Rig1 | RigW
  deriving (Show, Eq, Ord, Data, Generic, Typeable)

rigPlus :: RigCount -> RigCount -> RigCount
rigPlus Rig0 Rig0 = Rig0
rigPlus Rig0 Rig1 = Rig1
rigPlus Rig0 RigW = RigW
rigPlus Rig1 Rig0 = Rig1
rigPlus Rig1 Rig1 = RigW
rigPlus Rig1 RigW = RigW
rigPlus RigW Rig0 = RigW
rigPlus RigW Rig1 = RigW
rigPlus RigW RigW = RigW

rigMult :: RigCount -> RigCount -> RigCount
rigMult Rig0 Rig0 = Rig0
rigMult Rig0 Rig1 = Rig0
rigMult Rig0 RigW = Rig0
rigMult Rig1 Rig0 = Rig0
rigMult Rig1 Rig1 = Rig1
rigMult Rig1 RigW = RigW
rigMult RigW Rig0 = Rig0
rigMult RigW Rig1 = RigW
rigMult RigW RigW = RigW

type EnvTT n = [(n, RigCount, Binder (TT n))]

fstEnv (n, c, b) = n
rigEnv (n, c, b) = c
sndEnv (n, c, b) = b

envBinders = map (\(n, _, b) -> (n, b))
envZero = map (\(n, _, b) -> (n, Rig0, b))

lookupBinder :: Eq n => n -> EnvTT n -> Maybe (Binder (TT n))
lookupBinder n = lookup n . envBinders

data Datatype n = Data { d_typename :: n,
                         d_typetag  :: Int,
                         d_type     :: (TT n),
                         d_unique   :: Bool,
                         d_cons     :: [(n, TT n)] }
  deriving (Show, Functor, Eq)

-- | Data declaration options
data DataOpt = Codata -- ^ Set if the the data-type is coinductive
             | DefaultEliminator -- ^ Set if an eliminator should be generated for data type
             | DefaultCaseFun -- ^ Set if a case function should be generated for data type
             | DataErrRev
    deriving (Show, Eq, Generic)

type DataOpts = [DataOpt]

data TypeInfo = TI { con_names :: [Name],
                     codata :: Bool,
                     data_opts :: DataOpts,
                     param_pos :: [Int],
                     mutual_types :: [Name],
                     linear_con :: Bool -- is there a linear argument?
                   }
    deriving (Show, Generic)
{-!
deriving instance Binary TypeInfo
!-}

instance Eq n => Eq (TT n) where
    (==) (P xt x _)     (P yt y _)     = x == y
    (==) (V x)          (V y)          = x == y
    (==) (Bind _ xb xs) (Bind _ yb ys) = xs == ys && xb == yb
    (==) (App _ fx ax)  (App _ fy ay)  = ax == ay && fx == fy
    (==) (TType _)      (TType _)      = True -- deal with constraints later
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
isInjective (TType x)          = True
isInjective (Bind _ (Pi _ _ _ _) sc) = True
isInjective (App _ f a)        = isInjective f
isInjective _                  = False

-- | Count the number of instances of a de Bruijn index in a term
vinstances :: Int -> TT n -> Int
vinstances i (V x) | i == x = 1
vinstances i (App _ f a) = vinstances i f + vinstances i a
vinstances i (Bind x b sc) = instancesB b + vinstances (i + 1) sc
  where instancesB (Let t v) = vinstances i v
        instancesB _ = 0
vinstances i t = 0

-- | Replace the outermost (index 0) de Bruijn variable with the given term
instantiate :: TT n -> TT n -> TT n
instantiate e = subst 0 where
    subst i (P nt x ty) = P nt x (subst i ty)
    subst i (V x) | i == x = e
    subst i (Bind x b sc) = Bind x (fmap (subst i) b) (subst (i+1) sc)
    subst i (App s f a) = App s (subst i f) (subst i a)
    subst i (Proj x idx) = Proj (subst i x) idx
    subst i t = t

-- | As 'instantiate', but also decrement the indices of all de Bruijn variables
-- remaining in the term, so that there are no more references to the variable
-- that has been substituted.
substV :: TT n -> TT n -> TT n
substV x tm = dropV 0 (instantiate x tm) where
    dropV i (P nt x ty) = P nt x (dropV i ty)
    dropV i (V x) | x > i = V (x - 1)
                  | otherwise = V x
    dropV i (Bind x b sc) = Bind x (fmap (dropV i) b) (dropV (i+1) sc)
    dropV i (App s f a) = App s (dropV i f) (dropV i a)
    dropV i (Proj x idx) = Proj (dropV i x) idx
    dropV i t = t

-- | Replace all non-free de Bruijn references in the given term with references
-- to the name of their binding.
explicitNames :: TT n -> TT n
explicitNames (Bind x b sc) = let b' = fmap explicitNames b in
                                  Bind x b'
                                     (explicitNames (instantiate
                                        (P Bound x (binderTy b')) sc))
explicitNames (App s f a) = App s (explicitNames f) (explicitNames a)
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
pToV' n i (App s f a) = App s (pToV' n i f) (pToV' n i a)
pToV' n i (Proj t idx) = Proj (pToV' n i t) idx
pToV' n i t = t

-- increase de Bruijn indices, as if a binder has been added
addBinder :: TT n -> TT n
addBinder t = ab 0 t
  where
     ab top (V i) | i >= top = V (i + 1)
                  | otherwise = V i
     ab top (Bind x b sc) = Bind x (fmap (ab top) b) (ab (top + 1) sc)
     ab top (App s f a) = App s (ab top f) (ab top a)
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
    vToP' env (App s f a) = App s (vToP' env f) (vToP' env a)
    vToP' env t = t

-- | Replace every non-free reference to the name of a binding in
-- the given term with a de Bruijn index.
finalise :: Eq n => TT n -> TT n
finalise (Bind x b sc) = Bind x (fmap finalise b) (pToV x (finalise sc))
finalise (App s f a) = App s (finalise f) (finalise a)
finalise t = t

-- Once we've finished checking everything about a term we no longer need
-- the type on the 'P' so erase it so save memory

pEraseType :: TT n -> TT n
pEraseType (P nt t _) = P nt t Erased
pEraseType (App s f a) = App s (pEraseType f) (pEraseType a)
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
    subst' i t@(P nt x ty)
         = let (ty', ut) = subst' i ty in
               if ut then (P nt x ty', True) else (t, False)
    subst' i t@(Bind x b sc) | x /= n
         = let (b', ub) = substB' i b
               (sc', usc) = subst' (i+1) sc in
               if ub || usc then (Bind x b' sc', True) else (t, False)
    subst' i t@(App s f a) = let (f', uf) = subst' i f
                                 (a', ua) = subst' i a in
                                 if uf || ua then (App s f' a', True) else (t, False)
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
   s' i (App st f a) = App st (s' i f) (s' i a)
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
  st t | eqAlpha [] t old = new
  st (App s f a) = App s (st f) (st a)
  st (Bind x b sc) = Bind x (fmap st b) (st sc)
  st t = t

  eqAlpha as (P _ x _) (P _ y _)
       = x == y || (x, y) `elem` as || (y, x) `elem` as
  eqAlpha as (V x) (V y) = x == y
  eqAlpha as (Bind x xb xs) (Bind y yb ys)
       = eqAlphaB as xb yb && eqAlpha ((x, y) : as) xs ys
  eqAlpha as (App _ fx ax) (App _ fy ay) = eqAlpha as fx fy && eqAlpha as ax ay
  eqAlpha as x y = x == y

  eqAlphaB as (Let xt xv) (Let yt yv)
       = eqAlpha as xt yt && eqAlpha as xv yv
  eqAlphaB as (Guess xt xv) (Guess yt yv)
       = eqAlpha as xt yt && eqAlpha as xv yv
  eqAlphaB as bx by = eqAlpha as (binderTy bx) (binderTy by)

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
    no' i (App _ f a) = do no' i f; no' i a
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
    no' i (App _ f a) = no' i f && no' i a
    no' i (Proj x _) = no' i x
    no' i _ = True

-- | Returns all names used free in the term
freeNames :: Eq n => TT n -> [n]
freeNames t = nub $ freeNames' t
  where
    freeNames' (P _ n _) = [n]
    freeNames' (Bind n (Let t v) sc) = freeNames' v ++ (freeNames' sc \\ [n])
                                            ++ freeNames' t
    freeNames' (Bind n b sc) = freeNames' (binderTy b) ++ (freeNames' sc \\ [n])
    freeNames' (App _ f a) = freeNames' f ++ freeNames' a
    freeNames' (Proj x i) = freeNames' x
    freeNames' _ = []

-- | Return the arity of a (normalised) type
arity :: TT n -> Int
arity (Bind n (Pi _ _ t _) sc) = 1 + arity sc
arity _ = 0

-- | Deconstruct an application; returns the function and a list of arguments
unApply :: TT n -> (TT n, [TT n])
unApply t = ua [] t where
    ua args (App _ f a) = ua (a:args) f
    ua args t         = (t, args)

-- | Returns a term representing the application of the first argument
-- (a function) to every element of the second argument.
mkApp :: TT n -> [TT n] -> TT n
mkApp f [] = f
mkApp f (a:as) = mkApp (App MaybeHoles f a) as

unList :: Term -> Maybe [Term]
unList tm = case unApply tm of
              (nil, [_]) -> Just []
              (cons, ([_, x, xs])) ->
                  do rest <- unList xs
                     return $ x:rest
              (f, args) -> Nothing

-- | Hard-code a heuristic maximum term size, to prevent attempts to
-- serialize or force infinite or just gigantic terms
termSmallerThan :: Int -> Term -> Bool
termSmallerThan x tm | x <= 0 =  False
termSmallerThan x (P _ _ ty) = termSmallerThan (x-1) ty
termSmallerThan x (Bind _ _ tm) = termSmallerThan (x-1) tm
termSmallerThan x (App _ f a) = termSmallerThan (x-1) f && termSmallerThan (x-1) a
termSmallerThan x (Proj tm _) = termSmallerThan (x-1) tm
termSmallerThan x (V i) = True
termSmallerThan x (Constant c) = True
termSmallerThan x Erased = True
termSmallerThan x Impossible = True
termSmallerThan x (Inferred t) = termSmallerThan x t
termSmallerThan x (TType u) = True
termSmallerThan x (UType u) = True


-- | Cast a 'TT' term to a 'Raw' value, discarding universe information and
-- the types of named references and replacing all de Bruijn indices
-- with the corresponding name. It is an error if there are free de
-- Bruijn indices.
forget :: TT Name -> Raw
forget tm = forgetEnv [] tm

safeForget :: TT Name -> Maybe Raw
safeForget tm = safeForgetEnv [] tm

forgetEnv :: [Name] -> TT Name -> Raw
forgetEnv env tm = case safeForgetEnv env tm of
                     Just t' -> t'
                     Nothing -> error $ "Scope error in " ++ show tm ++ show env


safeForgetEnv :: [Name] -> TT Name -> Maybe Raw
safeForgetEnv env (P _ n _) = Just $ Var n
safeForgetEnv env (V i) | i < length env = Just $ Var (env !! i)
                        | otherwise = Nothing
safeForgetEnv env (Bind n b sc)
     = do let n' = uniqueName n env
          b' <- safeForgetEnvB env b
          sc' <- safeForgetEnv (n':env) sc
          Just $ RBind n' b' sc'
  where safeForgetEnvB env (Let t v) = liftM2 Let (safeForgetEnv env t)
                                                  (safeForgetEnv env v)
        safeForgetEnvB env (Guess t v) = liftM2 Guess (safeForgetEnv env t)
                                                      (safeForgetEnv env v)
        safeForgetEnvB env b = do ty' <- safeForgetEnv env (binderTy b)
                                  Just $ fmap (\_ -> ty') b
safeForgetEnv env (App _ f a) = liftM2 RApp (safeForgetEnv env f) (safeForgetEnv env a)
safeForgetEnv env (Constant c) = Just $ RConstant c
safeForgetEnv env (TType i) = Just RType
safeForgetEnv env (UType u) = Just $ RUType u
safeForgetEnv env Erased    = Just $ RConstant Forgot
safeForgetEnv env (Proj tm i) = error "Don't know how to forget a projection"
safeForgetEnv env Impossible = error "Don't know how to forget Impossible"
safeForgetEnv env (Inferred t) = safeForgetEnv env t

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
getArgTys (Bind n (PVar _ _) sc) = getArgTys sc
getArgTys (Bind n (PVTy _) sc) = getArgTys sc
getArgTys (Bind n (Pi _ _ t _) sc) = (n, t) : getArgTys sc
getArgTys _ = []

getRetTy :: TT n -> TT n
getRetTy (Bind n (PVar _ _) sc) = getRetTy sc
getRetTy (Bind n (PVTy _) sc) = getRetTy sc
getRetTy (Bind n (Pi _ _ _ _) sc)   = getRetTy sc
getRetTy sc = sc

-- | As getRetTy but substitutes names for de Bruijn indices
substRetTy :: TT n -> TT n
substRetTy (Bind n (PVar _ ty) sc) = substRetTy (substV (P Ref n ty) sc)
substRetTy (Bind n (PVTy ty) sc) = substRetTy (substV (P Ref n ty) sc)
substRetTy (Bind n (Pi _ _ ty _) sc) = substRetTy (substV (P Ref n ty) sc)
substRetTy sc = sc


uniqueNameFrom :: [Name] -> [Name] -> Name
uniqueNameFrom []           hs = uniqueName (nextName (sUN "x")) hs
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
    ubSet ns (App s f a) = App s (ubSet ns f) (ubSet ns a)
    ubSet ns t = t


nextName :: Name -> Name
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
    nextName' (ImplementationN n ns) = ImplementationN (nextName n) ns
    nextName' (ParentN n ns) = ParentN (nextName n) ns
    nextName' (CaseN fc n) = CaseN fc (nextName n)
    nextName' (ElimN n) = ElimN (nextName n)
    nextName' (MethodN n) = MethodN (nextName n)
    nextName' (ImplementationCtorN n) = ImplementationCtorN (nextName n)
    nextName' (MetaN parent meta) = MetaN parent (nextName meta)
nextName (SymRef i) = error "Can't generate a name from a symbol reference"

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
    show (AType ATFloat) = "Double"
    show (AType (ATInt ITBig)) = "Integer"
    show (AType (ATInt ITNative)) = "Int"
    show (AType (ATInt ITChar)) = "Char"
    show (AType (ATInt (ITFixed it))) = itBitsName it
    show TheWorld = "prim__TheWorld"
    show WorldType = "prim__WorldType"
    show StrType = "String"
    show VoidType = "Void"
    show Forgot = "Forgot"

showEnv :: (Eq n, Show n) => EnvTT n -> TT n -> String
showEnv env t = showEnv' env t False
showEnvDbg env t = showEnv' env t True

prettyEnv :: Env -> Term -> Doc OutputAnnotation
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
          text . show . fstEnv $ env!!i
        else
          lbracket <+> text (show i) <+> rbracket
      | otherwise      = text "unbound" <+> text (show i) <+> text "!"
    prettySe p env (Bind n b@(Pi _ _ t _) sc) debug
      | noOccurrence n sc && not debug =
          bracket p 2 $ prettySb env n b debug <> prettySe 10 ((n, Rig0, b):env) sc debug
    prettySe p env (Bind n b sc) debug =
      bracket p 2 $ prettySb env n b debug <> prettySe 10 ((n, Rig0, b):env) sc debug
    prettySe p env (App _ f a) debug =
      bracket p 1 $ prettySe 1 env f debug <+> prettySe 0 env a debug
    prettySe p env (Proj x i) debug =
      prettySe 1 env x debug <+> text ("!" ++ show i)
    prettySe p env (Constant c) debug = pretty c
    prettySe p env Erased debug = text "[_]"
    prettySe p env (TType i) debug = text "Type" <+> (text . show $ i)
    prettySe p env Impossible debug = text "Impossible"
    prettySe p env (Inferred tm) debug = text "<" <+> prettySe p env tm debug <+> text ">"
    prettySe p env (UType u) debug = text (show u)

    -- Render a `Binder` and its name
    prettySb env n (Lam _ t) = prettyB env "λ" "=>" n t
    prettySb env n (Hole t) = prettyB env "?defer" "." n t
    prettySb env n (GHole _ _ t) = prettyB env "?gdefer" "." n t
    prettySb env n (Pi Rig0 _ t _) = prettyB env "(" ") ->" n t
    prettySb env n (Pi Rig1 _ t _) = prettyB env "(" ") -o" n t
    prettySb env n (Pi RigW _ t _) = prettyB env "(" ") ->" n t
    prettySb env n (PVar Rig1 t) = prettyB env "pat 1 " "." n t
    prettySb env n (PVar _ t) = prettyB env "pat" "." n t
    prettySb env n (PVTy t) = prettyB env "pty" "." n t
    prettySb env n (Let t v) = prettyBv env "let" "in" n t v
    prettySb env n (NLet t v) = prettyBv env "nlet" "in" n t v
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
                                    = (show $ fstEnv $ env!!i) ++
                                      if dbg then "{" ++ show i ++ "}" else ""
                   | otherwise = "!!V " ++ show i ++ "!!"
    se p env (Bind n b@(Pi rig (Just _) t k) sc)
         = bracket p 2 $ sb env n b ++ se 10 ((n, rig, b):env) sc
    se p env (Bind n b@(Pi rig _ t k) sc)
        | noOccurrence n sc && not dbg = bracket p 2 $ se 1 env t ++ arrow rig ++ se 10 ((n,Rig0,b):env) sc
       where arrow Rig0 = " -> "
             arrow Rig1 = " -o "
             arrow RigW = " -> "
    se p env (Bind n b sc) = bracket p 2 $ sb env n b ++ se 10 ((n,Rig0,b):env) sc
    se p env (App _ f a) = bracket p 1 $ se 1 env f ++ " " ++ se 0 env a
    se p env (Proj x i) = se 1 env x ++ "!" ++ show i
    se p env (Constant c) = show c
    se p env Erased = "[__]"
    se p env Impossible = "[impossible]"
    se p env (Inferred t) = "<" ++ se p env t ++ ">"
    se p env (TType i) = "Type " ++ show i
    se p env (UType u) = show u

    sb env n (Lam Rig1 t)  = showb env "\\ 1 " " => " n t
    sb env n (Lam _ t)  = showb env "\\ " " => " n t
    sb env n (Hole t) = showb env "? " ". " n t
    sb env n (GHole i ns t) = showb env "?defer " ". " n t
    sb env n (Pi Rig1 (Just _) t _)   = showb env "{" "} -o " n t
    sb env n (Pi _ (Just _) t _)   = showb env "{" "} -> " n t
    sb env n (Pi Rig1 _ t _)   = showb env "(" ") -0 " n t
    sb env n (Pi _ _ t _)   = showb env "(" ") -> " n t
    sb env n (PVar Rig0 t) = showb env "pat 0 " ". " n t
    sb env n (PVar Rig1 t) = showb env "pat 1 " ". " n t
    sb env n (PVar _ t) = showb env "pat " ". " n t
    sb env n (PVTy t) = showb env "pty " ". " n t
    sb env n (Let t v)   = showbv env "let " " in " n t v
    sb env n (NLet t v)   = showbv env "nlet " " in " n t v
    sb env n (Guess t v) = showbv env "?? " " in " n t v

    showb env op sc n t    = op ++ show n ++ " : " ++ se 10 env t ++ sc
    showbv env op sc n t v = op ++ show n ++ " : " ++ se 10 env t ++ " = " ++
                             se 10 env v ++ sc

    bracket outer inner str | inner > outer = "(" ++ str ++ ")"
                            | otherwise = str

-- | Check whether a term has any hole bindings in it - impure if so
pureTerm :: TT Name -> Bool
pureTerm (App _ f a) = pureTerm f && pureTerm a
pureTerm (Bind n b sc) = notInterfaceName n && pureBinder b && pureTerm sc where
    pureBinder (Hole _) = False
    pureBinder (Guess _ _) = False
    pureBinder (Let t v) = pureTerm t && pureTerm v
    pureBinder t = pureTerm (binderTy t)

    notInterfaceName (MN _ c) | c == txt "__interface" = False
    notInterfaceName _ = True

pureTerm _ = True

-- | Weaken a term by adding i to each de Bruijn index (i.e. lift it over i bindings)
weakenTm :: Int -> TT n -> TT n
weakenTm i t = wk i 0 t
  where wk i min (V x) | x >= min = V (i + x)
        wk i m (App s f a)   = App s (wk i m f) (wk i m a)
        wk i m (Bind x b sc) = Bind x (wkb i m b) (wk i (m + 1) sc)
        wk i m t = t
        wkb i m t           = fmap (wk i m) t

-- | Weaken an environment so that all the de Bruijn indices are correct according
-- to the latest bound variable

weakenEnv :: EnvTT n -> EnvTT n
weakenEnv env = wk (length env - 1) env
  where wk i [] = []
        wk i ((n, c, b) : bs) = (n, c, weakenTmB i b) : wk (i - 1) bs
        weakenTmB i (Let   t v) = Let (weakenTm i t) (weakenTm i v)
        weakenTmB i (Guess t v) = Guess (weakenTm i t) (weakenTm i v)
        weakenTmB i t           = t { binderTy = weakenTm i (binderTy t) }

-- | Weaken every term in the environment by the given amount
weakenTmEnv :: Int -> EnvTT n -> EnvTT n
weakenTmEnv i = map (\ (n, c, b) -> (n, c, fmap (weakenTm i) b))

refsIn :: TT Name -> [Name]
refsIn (P _ n _) = [n]
refsIn (Bind n b t) = nub $ nb b ++ refsIn t
  where nb (Let   t v) = nub (refsIn t) ++ nub (refsIn v)
        nb (Guess t v) = nub (refsIn t) ++ nub (refsIn v)
        nb t = refsIn (binderTy t)
refsIn (App s f a) = nub (refsIn f ++ refsIn a)
refsIn _ = []

allTTNames :: Eq n => TT n -> [n]
allTTNames = nub . allNamesIn
  where allNamesIn (P _ n _) = [n]
        allNamesIn (Bind n b t) = [n] ++ nb b ++ allNamesIn t
          where nb (Let   t v) = allNamesIn t ++ allNamesIn v
                nb (Guess t v) = allNamesIn t ++ allNamesIn v
                nb t = allNamesIn (binderTy t)
        allNamesIn (App _ f a) = allNamesIn f ++ allNamesIn a
        allNamesIn _ = []


-- | Pretty-print a term
pprintTT :: [Name]  -- ^ The bound names (for highlighting and de Bruijn indices)
         -> TT Name -- ^ The term to be printed
         -> Doc OutputAnnotation
pprintTT bound tm = pp startPrec bound tm

  where
    startPrec = 0
    appPrec   = 10

    pp p bound (P Bound n ty) = annotate (AnnBoundName n False) (text $ show n)
    pp p bound (P nt n ty) = annotate (AnnName n Nothing Nothing Nothing)
                                          (text $ show n)
    pp p bound (V i)
       | i < length bound = let n = bound !! i
                            in annotate (AnnBoundName n False) (text $ show n)
       | otherwise        = text ("{{{V" ++ show i ++ "}}}")
    pp p bound (Bind n b sc) = ppb p bound n b $
                               pp startPrec (n:bound) sc
    pp p bound (App _ tm1 tm2) =
      bracket p appPrec . group . hang 2 $
        pp appPrec bound tm1 <> line <>
        pp (appPrec + 1) bound tm2
    pp p bound (Constant c) = annotate (AnnConst c) (text (show c))
    pp p bound (Proj tm i) =
      lparen <> pp startPrec bound tm <> rparen <>
      text "!" <> text (show i)
    pp p bound Erased = text "<<<erased>>>"
    pp p bound Impossible = text "<<<impossible>>>"
    pp p bound (Inferred t) = text "<" <+> pp p bound t <+> text ">"
    pp p bound (TType ue) = annotate (AnnType "Type" "The type of types") $
                            text "Type"
    pp p bound (UType u) = text (show u)

    ppb p bound n (Lam rig ty) sc =
      bracket p startPrec . group . align . hang 2 $
      text "λ" <+> bindingOf n False <+> text "." <> line <> sc
    ppb p bound n (Pi rig _ ty k) sc =
      bracket p startPrec . group . align $
      lparen <> (bindingOf n False) <+> colon <+>
      (group . align) (pp startPrec bound ty) <>
      rparen <+> mkArrow rig <> line <> sc
        where mkArrow Rig1 = text "⇴"
              mkArrow Rig0 = text "⥛"
              mkArrow _ = text "→"
    ppb p bound n (Let ty val) sc =
      bracket p startPrec . group . align $
      (group . hang 2) (annotate AnnKeyword (text "let") <+>
                        bindingOf n False <+> colon <+>
                        pp startPrec bound ty <+>
                        text "=" <> line <>
                        pp startPrec bound val) <> line <>
      (group . hang 2) (annotate AnnKeyword (text "in") <+> sc)
    ppb p bound n (NLet ty val) sc =
      bracket p startPrec . group . align $
      (group . hang 2) (annotate AnnKeyword (text "nlet") <+>
                        bindingOf n False <+> colon <+>
                        pp startPrec bound ty <+>
                        text "=" <> line <>
                        pp startPrec bound val) <> line <>
      (group . hang 2) (annotate AnnKeyword (text "in") <+> sc)
    ppb p bound n (Hole ty) sc =
      bracket p startPrec . group . align . hang 2 $
      text "?" <+> bindingOf n False <+> text "." <> line <> sc
    ppb p bound n (GHole _ _ ty) sc =
      bracket p startPrec . group . align . hang 2 $
      text "¿" <+> bindingOf n False <+> text "." <> line <> sc
    ppb p bound n (Guess ty val) sc =
      bracket p startPrec . group . align . hang 2 $
      text "?" <> bindingOf n False <+>
      text "≈" <+> pp startPrec bound val <+>
      text "." <> line <> sc
    ppb p bound n (PVar _ ty) sc =
      bracket p startPrec . group . align . hang 2 $
      annotate AnnKeyword (text "pat") <+>
      bindingOf n False <+> colon <+> pp startPrec bound ty <+>
      text "." <> line <>
      sc
    ppb p bound n (PVTy ty) sc =
      bracket p startPrec . group . align . hang 2 $
      annotate AnnKeyword (text "patTy") <+>
      bindingOf n False <+> colon <+> pp startPrec bound ty <+>
      text "." <> line <>
      sc

    bracket outer inner doc
      | outer > inner = lparen <> doc <> rparen
      | otherwise     = doc

pprintTTClause :: [(Name, Type)] -> Term -> Term -> Doc OutputAnnotation
pprintTTClause pvars lhs rhs =
    vars pvars . group . align $
      pprintTT (map fst pvars) lhs <$>
      text "↦" <$>
      (pprintTT (map fst pvars) rhs)
  where vars [] terms = terms
        vars (v:vs) terms =
          annotate AnnKeyword (text "var") <+>
          group (align (sep (punctuate comma (reverse (bindVars [] (v:vs)))))) <+>
          annotate AnnKeyword (text ".") <$>
          indent 2 terms
        bindVars _ [] = []
        bindVars ns ((n, ty):vs) =
          bindingOf n False <+> colon <+> pprintTT ns ty : bindVars (n:ns) vs


-- | Pretty-print a raw term.
pprintRaw :: [Name] -- ^ Bound names, for highlighting
          -> Raw -- ^ The term to pretty-print
          -> Doc OutputAnnotation
pprintRaw bound (Var n) =
  enclose lparen rparen . group . align . hang 2 $
    (text "Var") <$> annotate (if n `elem` bound
                                  then AnnBoundName n False
                                  else AnnName n Nothing Nothing Nothing)
                              (text $ show n)
pprintRaw bound (RBind n b body) =
  enclose lparen rparen . group . align . hang 2 $
  vsep [ text "RBind"
       , annotate (AnnBoundName n False) (text $ show n)
       , ppb b
       , pprintRaw (n:bound) body]
  where
    ppb (Lam _ ty) = enclose lparen rparen . group . align . hang 2 $
                     text "Lam" <$> pprintRaw bound ty
    ppb (Pi _ _ ty k) = enclose lparen rparen . group . align . hang 2 $
                        vsep [text "Pi", pprintRaw bound ty, pprintRaw bound k]
    ppb (Let ty v) = enclose lparen rparen . group . align . hang 2 $
                     vsep [text "Let", pprintRaw bound ty, pprintRaw bound v]
    ppb (NLet ty v) = enclose lparen rparen . group . align . hang 2 $
                      vsep [text "NLet", pprintRaw bound ty, pprintRaw bound v]
    ppb (Hole ty) = enclose lparen rparen . group . align . hang 2 $
                    text "Hole" <$> pprintRaw bound ty
    ppb (GHole _ _ ty) = enclose lparen rparen . group . align . hang 2 $
                         text "GHole" <$> pprintRaw bound ty
    ppb (Guess ty v) = enclose lparen rparen . group . align . hang 2 $
                       vsep [text "Guess", pprintRaw bound ty, pprintRaw bound v]
    ppb (PVar _ ty) = enclose lparen rparen . group . align . hang 2 $
                      text "PVar" <$> pprintRaw bound ty
    ppb (PVTy ty) = enclose lparen rparen . group . align . hang 2 $
                    text "PVTy" <$> pprintRaw bound ty
pprintRaw bound (RApp f x) =
  enclose lparen rparen . group . align . hang 2 . vsep $
  [text "RApp", pprintRaw bound f, pprintRaw bound x]
pprintRaw bound RType = text "RType"
pprintRaw bound (RUType u) = enclose lparen rparen . group . align . hang 2 $
                             text "RUType" <$> text (show u)
pprintRaw bound (RConstant c) =
  enclose lparen rparen . group . align . hang 2 $
  vsep [text "RConstant", annotate (AnnConst c) (text (show c))]

-- | Pretty-printer helper for the binding site of a name
bindingOf :: Name -- ^^ the bound name
          -> Bool -- ^^ whether the name is implicit
          -> Doc OutputAnnotation
bindingOf n imp = annotate (AnnBoundName n imp) (text (show n))

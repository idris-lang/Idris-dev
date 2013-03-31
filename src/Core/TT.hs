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

module Core.TT where

import Control.Monad.State
import Debug.Trace
import qualified Data.Map as Map
import Data.Char
import Data.List
import qualified Data.Binary as B
import Data.Binary hiding (get, put)

import Util.Pretty hiding (Str)

data Option = TTypeInTType
            | CheckConv
  deriving Eq

-- | Source location. These are typically produced by the parser 'Idris.Parser.pfc'
data FC = FC { fc_fname :: String, -- ^ Filename
               fc_line :: Int -- ^ Line number
             }
    deriving Eq
{-! 
deriving instance Binary FC 
!-}

instance Sized FC where
  size (FC f l) = 1 + length f

instance Show FC where
    show (FC f l) = f ++ ":" ++ show l

data Err = Msg String
         | InternalMsg String
         | CantUnify Bool Term Term Err [(Name, Type)] Int 
              -- Int is 'score' - how much we did unify
              -- Bool indicates recoverability, True indicates more info may make
              -- unification succeed
         | InfiniteUnify Name Term [(Name, Type)]
         | CantConvert Term Term [(Name, Type)]
         | NonFunctionType Term Term
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
         | ProviderError String
  deriving Eq

instance Sized Err where
  size (Msg msg) = length msg
  size (InternalMsg msg) = length msg
  size (CantUnify _ left right err _ score) = size left + size right + size err
  size (InfiniteUnify _ right _) = size right
  size (CantConvert left right _) = size left + size right
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
  size (ProviderError msg) = length msg
  size _ = 1

score :: Err -> Int
score (CantUnify _ _ _ m _ s) = s + score m
score (CantResolve _) = 20
score (NoSuchVariable _) = 1000
score (ProofSearchFail _) = 10000
score _ = 0

instance Show Err where
    show (Msg s) = s
    show (InternalMsg s) = "Internal error: " ++ show s
    show (CantUnify _ l r e sc i) = "CantUnify " ++ show l ++ " " ++ show r ++ " "
                                      ++ show e ++ " in " ++ show sc ++ " " ++ show i
    show (Inaccessible n) = show n ++ " is not an accessible pattern variable"
    show (ProviderError msg) = "Type provider error: " ++ msg
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
  pretty _ = text "Error"

data TC a = OK a
          | Error Err
  deriving (Eq, Functor)

instance Pretty a => Pretty (TC a) where
  pretty (OK ok) = pretty ok
  pretty (Error err) =
    if size err > breakingSize then
      text "Error" <+> colon $$ (nest nestingSize $ pretty err)
    else
      text "Error" <+> colon <+> pretty err

instance Show a => Show (TC a) where
    show (OK x) = show x
    show (Error str) = "Error: " ++ show str

-- at some point, this instance should also carry type checking options
-- (e.g. Type:Type)

instance Monad TC where
    return = OK 
    x >>= k = case x of 
                OK v -> k v
                Error e -> Error e
    fail e = Error (InternalMsg e)

tfail :: Err -> TC a
tfail e = Error e

trun :: FC -> TC a -> TC a
trun fc (OK a)    = OK a
trun fc (Error e) = Error (At fc e) 

instance MonadPlus TC where
    mzero = fail "Unknown error"
    (OK x) `mplus` _ = OK x
    _ `mplus` (OK y) = OK y
    err `mplus` _    = err

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
data Name = UN String -- ^ User-provided name
          | NS Name [String] -- ^ Root, namespaces 
          | MN Int String -- ^ Machine chosen names
          | NErased -- ^ Name of somethng which is never used in scope
  deriving (Eq, Ord)
{-! 
deriving instance Binary Name 
!-}

instance Sized Name where
  size (UN n)     = 1
  size (NS n els) = 1 + length els
  size (MN i n) = 1
  size NErased = 1

instance Pretty Name where
  pretty (UN n) = text n
  pretty (NS n s) = pretty n
  pretty (MN i s) = lbrace <+> text s <+> (text . show $ i) <+> rbrace

instance Show Name where
    show (UN n) = n
    show (NS n s) = showSep "." (reverse s) ++ "." ++ show n
    show (MN i s) = "{" ++ s ++ show i ++ "}"
    show NErased = "_"

-- |Contexts allow us to map names to things. A root name maps to a collection
-- of things in different namespaces with that name.
type Ctxt a = Map.Map Name (Map.Map Name a)
emptyContext = Map.empty

tcname (UN ('@':_)) = True
tcname (NS n _) = tcname n
tcname _ = False

implicitable (NS n _) = implicitable n
implicitable (UN (x:xs)) = isLower x
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

lookupCtxtName :: Maybe [String] -> Name -> Ctxt a -> [(Name, a)]
lookupCtxtName nspace n ctxt = case Map.lookup (nsroot n) ctxt of
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

lookupCtxt :: Maybe [String] -> Name -> Ctxt a -> [a]
lookupCtxt ns n ctxt = map snd (lookupCtxtName ns n ctxt)

updateDef :: Name -> (a -> a) -> Ctxt a -> Ctxt a
updateDef n f ctxt 
  = let ds = lookupCtxtName Nothing n ctxt in
        foldr (\ (n, t) c -> addDef n (f t) c) ctxt ds  

toAlist :: Ctxt a -> [(Name, a)]
toAlist ctxt = let allns = map snd (Map.toList ctxt) in
                concat (map (Map.toList) allns)

addAlist :: Show a => [(Name, a)] -> Ctxt a -> Ctxt a
addAlist [] ctxt = ctxt
addAlist ((n, tm) : ds) ctxt = addDef n tm (addAlist ds ctxt)

data Const = I Int | BI Integer | Fl Double | Ch Char | Str String 
           | IType | BIType     | FlType    | ChType  | StrType

           | B8 Word8 | B16 Word16 | B32 Word32 | B64 Word64
           | B8Type   | B16Type | B32Type | B64Type

           | PtrType | VoidType | Forgot
  deriving (Eq, Ord)
{-! 
deriving instance Binary Const 
!-}

instance Sized Const where
  size _ = 1

instance Pretty Const where
  pretty (I i) = text . show $ i
  pretty (BI i) = text . show $ i
  pretty (Fl f) = text . show $ f
  pretty (Ch c) = text . show $ c
  pretty (Str s) = text s
  pretty IType = text "Int"
  pretty BIType = text "BigInt"
  pretty FlType = text "Float"
  pretty ChType = text "Char"
  pretty StrType = text "String"
  pretty PtrType = text "Ptr"
  pretty VoidType = text "Void"
  pretty Forgot = text "Forgot"
  pretty B8Type = text "Bits8"
  pretty B16Type = text "Bits16"
  pretty B32Type = text "Bits32"
  pretty B64Type = text "Bits64"

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
!-}

-- | All binding forms are represented in a unform fashion.
data Binder b = Lam   { binderTy  :: b {-^ type annotation for bound variable-}}
              | Pi    { binderTy  :: b }
              | Let   { binderTy  :: b,
                        binderVal :: b {-^ value for bound variable-}}
              | NLet  { binderTy  :: b,
                        binderVal :: b }
              | Hole  { binderTy  :: b}
              | GHole { binderTy  :: b}
              | Guess { binderTy  :: b,
                        binderVal :: b }
              | PVar  { binderTy  :: b }
              | PVTy  { binderTy  :: b }
  deriving (Show, Eq, Ord, Functor)
{-! 
deriving instance Binary Binder 
!-}

instance Sized a => Sized (Binder a) where
  size (Lam ty) = 1 + size ty
  size (Pi ty) = 1 + size ty
  size (Let ty val) = 1 + size ty + size val
  size (NLet ty val) = 1 + size ty + size val
  size (Hole ty) = 1 + size ty
  size (GHole ty) = 1 + size ty
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
fmapMB f (GHole t)   = liftM GHole (f t)
fmapMB f (PVar t)    = liftM PVar (f t)
fmapMB f (PVTy t)    = liftM PVTy (f t)

raw_apply :: Raw -> [Raw] -> Raw
raw_apply f [] = f
raw_apply f (a : as) = raw_apply (RApp f a) as

raw_unapply :: Raw -> (Raw, [Raw])
raw_unapply t = ua [] t where
    ua args (RApp f a) = ua (a:args) f
    ua args t          = (t, args)

data RawFun = RawFun { rtype :: Raw,
                       rval  :: Raw
                     }
  deriving Show

data RawDatatype = RDatatype Name Raw [(Name, Raw)]
  deriving Show

data RDef = RFunction RawFun
          | RConst Raw
          | RData RawDatatype
  deriving Show

type RProgram = [(Name, RDef)]

-- WELL TYPED TERMS ---------------------------------------------------------

-- | Universe expressions for universe checking
data UExp = UVar Int -- ^ universe variable
          | UVal Int -- ^ explicit universe level
  deriving (Eq, Ord)

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

data NameType = Bound | Ref | DCon Int Int | TCon Int Int
  deriving (Show, Ord)
{-! 
deriving instance Binary NameType 
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

-- | Terms in the core language
data TT n = P NameType n (TT n) -- ^ named references
          | V Int -- ^ a resolved de Bruijn-indexed variable
          | Bind n (Binder (TT n)) (TT n) -- ^ a binding
          | App (TT n) (TT n) -- ^ function, function type, arg
          | Constant Const -- ^ constant
          | Proj (TT n) Int -- ^ argument projection; runtime only
          | Erased -- ^ an erased term
          | Impossible -- ^ special case for totality checking
          | TType UExp -- ^ the type of types at some level
  deriving (Ord, Functor)
{-! 
deriving instance Binary TT 
!-}

class TermSize a where
  termsize :: Name -> a -> Int

instance TermSize a => TermSize [a] where
    termsize n [] = 0
    termsize n (x : xs) = termsize n x + termsize n xs

instance TermSize (TT Name) where
    termsize n (P _ x _) 
       | x == n = 1000000 -- recursive => really big
       | otherwise = 1
    termsize n (V _) = 1
    termsize n (Bind n' (Let t v) sc) 
       = let rn = if n == n' then MN 0 "noname" else n in
             termsize rn v + termsize rn sc
    termsize n (App f a) = termsize n f + termsize n a
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
    (==) (Bind _ xb xs) (Bind _ yb ys) = xb == yb && xs == ys
    (==) (App fx ax)    (App fy ay)    = fx == fy && ax == ay
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

instantiate :: TT n -> TT n -> TT n
instantiate e = subst 0 where
    subst i (V x) | i == x = e
    subst i (Bind x b sc) = Bind x (fmap (subst i) b) (subst (i+1) sc)
    subst i (App f a) = App (subst i f) (subst i a)
    subst i (Proj x idx) = Proj (subst i x) idx 
    subst i t = t

explicitNames :: TT n -> TT n
explicitNames (Bind x b sc) = let b' = fmap explicitNames b in
                                  Bind x b'
                                     (explicitNames (instantiate 
                                        (P Bound x (binderTy b')) sc))
explicitNames (App f a) = App (explicitNames f) (explicitNames a)
explicitNames (Proj x idx) = Proj (explicitNames x) idx
explicitNames t = t

pToV :: Eq n => n -> TT n -> TT n
pToV n = pToV' n 0
pToV' n i (P _ x _) | n == x = V i
pToV' n i (Bind x b sc)
-- We can assume the inner scope has been pToVed already, so continue to
-- resolve names from the *outer* scope which may happen to have the same id.
--                 | n == x    = Bind x (fmap (pToV' n i) b) sc
     | otherwise = Bind x (fmap (pToV' n i) b) (pToV' n (i+1) sc)
pToV' n i (App f a) = App (pToV' n i f) (pToV' n i a)
pToV' n i (Proj t idx) = Proj (pToV' n i t) idx
pToV' n i t = t

-- | Convert several names. First in the list comes out as V 0
pToVs :: Eq n => [n] -> TT n -> TT n
pToVs ns tm = pToVs' ns tm 0 where
    pToVs' []     tm i = tm
    pToVs' (n:ns) tm i = pToV' n i (pToVs' ns tm (i+1))

vToP :: TT n -> TT n
vToP = vToP' [] where
    vToP' env (V i) = let (n, b) = (env !! i) in
                          P Bound n (binderTy b)
    vToP' env (Bind n b sc) = let b' = fmap (vToP' env) b in
                                  Bind n b' (vToP' ((n, b'):env) sc)
    vToP' env (App f a) = App (vToP' env f) (vToP' env a)
    vToP' env t = t

finalise :: Eq n => TT n -> TT n
finalise (Bind x b sc) = Bind x (fmap finalise b) (pToV x (finalise sc))
finalise (App f a) = App (finalise f) (finalise a)
finalise t = t

subst :: Eq n => n -> TT n -> TT n -> TT n
subst n v tm = instantiate v (pToV n tm)

substNames :: Eq n => [(n, TT n)] -> TT n -> TT n
substNames []             t = t
substNames ((n, tm) : xs) t = subst n tm (substNames xs t)

substTerm :: Eq n => TT n -> TT n -> TT n -> TT n
substTerm old new = st where
  st t | t == old = new
  st (App f a) = App (st f) (st a)
  st (Bind x b sc) = Bind x (fmap st b) (st sc)
  st t = t

-- Returns true if V 0 and bound name n do not occur in the term

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

mkApp :: TT n -> [TT n] -> TT n
mkApp f [] = f
mkApp f (a:as) = mkApp (App f a) as

forget :: TT Name -> Raw
forget tm = fe [] tm
  where
    fe env (P _ n _) = Var n
    fe env (V i)     = Var (env !! i)
    fe env (Bind n b sc) = RBind n (fmap (fe env) b) 
                                   (fe (n:env) sc)
    fe env (App f a) = RApp (fe env f) (fe env a)
    fe env (Constant c) 
                     = RConstant c
    fe env (TType i)   = RType
    fe env Erased    = RConstant Forgot 
    
bindAll :: [(n, Binder (TT n))] -> TT n -> TT n 
bindAll [] t =t
bindAll ((n, b) : bs) t = Bind n b (bindAll bs t)

bindTyArgs :: (TT n -> Binder (TT n)) -> [(n, TT n)] -> TT n -> TT n
bindTyArgs b xs = bindAll (map (\ (n, ty) -> (n, b ty)) xs)

getArgTys :: TT n -> [(n, TT n)]
getArgTys (Bind n (Pi t) sc) = (n, t) : getArgTys sc
getArgTys _ = []

getRetTy :: TT n -> TT n
getRetTy (Bind n (PVar _) sc) = getRetTy sc
getRetTy (Bind n (PVTy _) sc) = getRetTy sc
getRetTy (Bind n (Pi _) sc)   = getRetTy sc
getRetTy sc = sc

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
nextName (UN x) = let (num', nm') = span isDigit (reverse x)
                      nm = reverse nm'
                      num = readN (reverse num') in
                          UN (nm ++ show (num+1))
  where
    readN "" = 0
    readN x  = read x

type Term = TT Name
type Type = Term

type Env  = EnvTT Name

-- an environment with de Bruijn indices 'normalised' so that they all refer to
-- this environment

newtype WkEnvTT n = Wk (EnvTT n)
type WkEnv = WkEnvTT Name

instance (Eq n, Show n) => Show (TT n) where
    show t = showEnv [] t

instance Show Const where
    show (I i) = show i
    show (BI i) = show i ++ "L"
    show (Fl f) = show f
    show (Ch c) = show c
    show (Str s) = show s
    show (B8 x) = show x
    show (B16 x) = show x
    show (B32 x) = show x
    show (B64 x) = show x
    show IType = "Int"
    show BIType = "Integer"
    show FlType = "Float"
    show ChType = "Char"
    show StrType = "String"
    show PtrType = "Ptr"
    show B8Type = "Bits8"
    show B16Type = "Bits16"
    show B32Type = "Bits32"
    show B64Type = "Bits64"
    show VoidType = "Void"

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

    prettySb env n (Lam t) = prettyB env "λ" "=>" n t
    prettySb env n (Hole t) = prettyB env "?defer" "." n t
    prettySb env n (Pi t) = prettyB env "(" ") ->" n t
    prettySb env n (PVar t) = prettyB env "pat" "." n t
    prettySb env n (PVTy t) = prettyB env "pty" "." n t
    prettySb env n (Let t v) = prettyBv env "let" "in" n t v
    prettySb env n (Guess t v) = prettyBv env "??" "in" n t v

    prettyB env op sc n t debug =
      text op <> pretty n <+> colon <+> prettySe 10 env t debug <> text sc

    prettyBv env op sc n t v debug =
      text op <> pretty n <+> colon <+> prettySe 10 env t debug <+> text "=" <+>
        prettySe 10 env v debug <> text sc
          

showEnv' env t dbg = se 10 env t where
    se p env (P nt n t) = show n 
                            ++ if dbg then "{" ++ show nt ++ " : " ++ se 10 env t ++ "}" else ""
    se p env (V i) | i < length env = (show $ fst $ env!!i) ++
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
    sb env n (GHole t) = showb env "?defer " ". " n t
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

    notClassName (MN _ "class") = False
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

weakenTmEnv :: Int -> EnvTT n -> EnvTT n
weakenTmEnv i = map (\ (n, b) -> (n, fmap (weakenTm i) b))

orderPats :: Term -> Term
orderPats tm = op [] tm
  where
    op ps (Bind n (PVar t) sc) = op ((n, PVar t) : ps) sc
    op ps (Bind n (Hole t) sc) = op ((n, Hole t) : ps) sc
    op ps sc = bindAll (map (\ (n, t) -> (n, t)) (sortP ps)) sc 

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


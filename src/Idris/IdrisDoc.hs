{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Generation of HTML documentation for Idris code
module Idris.IdrisDoc (generateDocs) where

import Idris.Core.TT (Name (..), sUN, SpecialName (..), OutputAnnotation (..),
                      TextFormatting (..), txt, str, nsroot, constIsType)
import Idris.Core.Evaluate (ctxtAlist, Def (..), lookupDefAcc,
                            Accessibility (..), isDConName, isFnName,
                            isTConName)
import Idris.ParseHelpers (opChars)
import Idris.AbsSyntax
import Idris.Docs
import Idris.Docstrings (nullDocstring)

import IRTS.System (getDataFileName)

import Control.Monad (forM_)
import Control.Monad.Trans.Error
import Control.Monad.Trans.State.Strict

import Data.Maybe

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BS2
import qualified Data.Text.Encoding as E
import qualified Data.List as L
import qualified Data.List.Split as LS
import qualified Data.Map as M hiding ((!))
import qualified Data.Ord (compare)
import qualified Data.Set as S
import qualified Data.Text as T

import System.IO
import System.IO.Error
import System.FilePath
import System.Directory

import Cheapskate.Html (renderDoc)
import Text.PrettyPrint.Annotated.Leijen (displayDecorated, renderCompact)

import Text.Blaze (toValue, contents)
import Text.Blaze.Internal (MarkupM (Empty))
import Text.Blaze.Html5 ((!), toHtml, preEscapedToHtml)
import qualified Text.Blaze.Html5 as H
import Text.Blaze.Html5.Attributes as A
import Text.Blaze.Html.Renderer.Utf8 (renderHtml)
import qualified Text.Blaze.Html.Renderer.String as R
import Text.Blaze.Renderer.String (renderMarkup)

-- ---------------------------------------------------------------- [ Public ]

-- | Generates HTML documentation for a series of loaded namespaces
--   and their dependencies.
generateDocs :: IState   -- ^ IState where all necessary information is
                         --   extracted from.
             -> [Name]   -- ^ List of namespaces to generate
                         --   documentation for.
             -> FilePath -- ^ The directory to which documentation will
                         --   be written.
             -> IO (Either String ())
generateDocs ist nss' out =
  do let nss     = map toNsName nss'
     docs       <- fetchInfo ist nss
     let (c, io) = foldl (checker docs) (0, return ()) nss
     io
     if c < length nss
        then catchIOError (createDocs ist docs out) (err . show)
        else err "No namespaces to generate documentation for"

  where checker docs st ns | M.member ns docs = st
        checker docs (c, io) ns = (c+1, do prev <- io; warnMissing ns)
        warnMissing ns =
          putStrLn $ "Warning: Ignoring empty or non-existing namespace '" ++
                     (nsName2Str ns) ++ "'"

-- ----------------------------------------------------------------- [ Types ]

-- | Either an error message or a result
type Failable = Either String

-- | Internal representation of a fully qualified namespace name
type NsName   = [T.Text]

-- | All information to be documented about a single namespace member
type NsItem   = (Name, Maybe Docs, Accessibility)

-- | All information to be documented about a namespace
type NsInfo   = [NsItem]

-- | A map from namespace names to information about them
type NsDict   = M.Map NsName NsInfo

-- --------------------------------------------------------------- [ Utility ]

-- | Make an error message
err :: String -> IO (Failable ())
err s = return $ Left s

-- | IdrisDoc version
version :: String
version = "1.0"

-- | Converts a Name into a [Text] corresponding to the namespace
--   part of a NS Name.
toNsName :: Name -- ^ Name to convert
         -> NsName
toNsName (UN n)    = [n]
toNsName (NS n ns) = (toNsName n) ++ ns
toNsName _         = []


-- | Retrieves the namespace part of a Name
getNs :: Name -- ^ Name to retrieve namespace for
      -> NsName
getNs (NS _ ns) = ns
getNs _         = []


-- | String to replace for the root namespace
rootNsStr :: String
rootNsStr = "[builtins]"


-- | Converts a NsName to string form
nsName2Str :: NsName -- ^ NsName to convert
           -> String
nsName2Str n = if null n then rootNsStr else name n

  where name []       = []
        name [ns]     = str ns
        name (ns:nss) = (name nss) ++ ('.' : str ns)

-- --------------------------------------------------------- [ Info Fetching ]

-- | Fetch info about namespaces and their contents
fetchInfo :: IState    -- ^ IState to fetch info from
          -> [NsName]  -- ^ List of namespaces to fetch info for
          -> IO NsDict -- ^ Mapping from namespace name to
                       --   info about its contents
fetchInfo ist nss =
  do let originNss  = S.fromList nss
     info          <- nsDict ist
     let info'      = M.map (filter filterInclude) info
         info''     = M.map removeOrphans info'
         info'''    = M.filter (not . null) info''
         reachedNss = traceNss info''' originNss S.empty
     return $ M.filterWithKey (\k _ -> S.member k reachedNss) info'''


-- | Removes loose class methods and data constructors,
--   leaving them documented only under their parent.
removeOrphans :: [NsItem] -- ^ List to remove orphans from
              -> [NsItem] -- ^ Orphan-free list
removeOrphans list =
  let children = S.fromList $ concatMap (names . (\(_, d, _) -> d)) list
  in  filter ((`S.notMember` children) . (\(n, _, _) -> n)) list

  where names (Just (DataDoc _ fds))          = map (\(FD n _ _ _ _) -> n) fds
        names (Just (ClassDoc _ _ fds _ _ _)) = map (\(FD n _ _ _ _) -> n) fds
        names _                               = []

-- | Whether a Name names something which should be documented
filterName :: Name -- ^ Name to check
           -> Bool -- ^ Predicate result
filterName (UN n)     | '@':'@':_ <- str n = False
filterName (UN _)     = True
filterName (NS n _)   = filterName n
filterName _          = False


-- | Whether a NsItem should be included in the documentation.
--   It must not be Hidden and filterName must return True for the name.
--   Also it must have Docs -- without Docs, nothing can be done.
filterInclude :: NsItem -- ^ Accessibility to check
              -> Bool   -- ^ Predicate result
filterInclude (name, Just _, Public) | filterName name = True
filterInclude (name, Just _, Frozen) | filterName name = True
filterInclude _                                        = False


-- | Finds all namespaces indirectly referred by a set of namespaces.
--   The NsItems of the namespaces are searched for references.
traceNss :: NsDict       -- ^ Mappings of namespaces and their contents
         -> S.Set NsName -- ^ Set of namespaces to trace
         -> S.Set NsName -- ^ Set of namespaces which has been traced
         -> S.Set NsName -- ^ Set of namespaces to trace and all traced one
traceNss nsd sT sD =
  let nsTracer ns | Just nsis <- M.lookup ns nsd = map referredNss nsis
      nsTracer _                                 = [S.empty] -- Ignore
      reached     = S.unions $ concatMap nsTracer (S.toList sT)
      processed   = S.union sT sD
      untraced    = S.difference reached processed
  in  if S.null untraced then processed
      else traceNss nsd untraced processed


-- | Gets all namespaces directly referred by a NsItem
referredNss :: NsItem -- ^ The name to get all directly
                      --   referred namespaces for
            -> S.Set NsName
referredNss (_, Nothing, _) = S.empty
referredNss (n, Just d, _) =
  let fds    = getFunDocs d
      ts     = concatMap types fds
      names  = concatMap (extractPTermNames) ts
  in  S.map getNs $ S.fromList names

  where getFunDocs (FunDoc f)              = [f]
        getFunDocs (DataDoc f fs)          = f:fs
        getFunDocs (ClassDoc _ _ fs _ _ _) = fs
        types (FD _ _ args t _)            = t:(map second args)
        second (_, x, _, _)                = x


-- | Returns an NsDict of containing all known namespaces and their contents
nsDict :: IState
       -> IO NsDict
nsDict ist =
  let nameDefList    = ctxtAlist $ tt_ctxt ist
      adder m (n, _) = do map    <- m
                          doc    <- loadDocs ist n
                          let acc = getAccess ist n
                              c   = [(n, doc, acc)]
                          return $ M.insertWith (++) (getNs n) c map
  in  foldl adder (return M.empty) nameDefList


-- | Gets the Accessibility for a Name
getAccess :: IState        -- ^ IState containing accessibility information
          -> Name          -- ^ The Name to retrieve access for
          -> Accessibility
getAccess ist n =
  let res = lookupDefAcc n False (tt_ctxt ist)
  in case res of
     [(_, acc)] -> acc
     _          -> Hidden

-- | Simple predicate for whether an NsItem has Docs
hasDoc :: NsItem -- ^ The NsItem to test
       -> Bool   -- ^ The result
hasDoc (_, Just _, _) = True
hasDoc _              = False


-- | Predicate saying whether a Name possibly may have docs defined
--   Without this, getDocs from Idris.Docs may fail a pattern match.
mayHaveDocs :: Name -- ^ The Name to test
            -> Bool -- ^ The result
mayHaveDocs (UN _)   = True
mayHaveDocs (NS n _) = mayHaveDocs n
mayHaveDocs _        = False


-- | Retrieves the Docs for a Name
loadDocs :: IState     -- ^ IState to extract infomation from
         -> Name       -- ^ Name to load Docs for
         -> IO (Maybe Docs)
loadDocs ist n
  | mayHaveDocs n = do docs <- runErrorT $ evalStateT (getDocs n) ist
                       case docs of Right d -> return (Just d)
                                    Left _  -> return Nothing
  | otherwise     = return Nothing


-- | Extracts names referred from a type.
--   The covering of all PTerms ensures that we avoid unanticipated cases,
--   though all of them are not needed. The author just did not know which!
--   TODO: Remove unnecessary cases
extractPTermNames :: PTerm  -- ^ Where to extract names from
                  -> [Name] -- ^ Extracted names
extractPTermNames (PRef _ n)         = [n]
extractPTermNames (PInferRef _ n)    = [n]
extractPTermNames (PPatvar _ n)      = [n]
extractPTermNames (PLam n p1 p2)     = n : concatMap extract [p1, p2]
extractPTermNames (PPi _ n p1 p2)    = n : concatMap extract [p1, p2]
extractPTermNames (PLet n p1 p2 p3)  = n : concatMap extract [p1, p2, p3]
extractPTermNames (PTyped p1 p2)     = concatMap extract [p1, p2]
extractPTermNames (PApp _ p pas)     = let names = concatMap extractPArg pas
                                       in  (extract p) ++ names
extractPTermNames (PAppBind _ p pas) = let names = concatMap extractPArg pas
                                       in  (extract p) ++ names
extractPTermNames (PMatchApp _ n)    = [n]
extractPTermNames (PCase _ p ps)     = let (ps1, ps2) = unzip ps
                                       in  concatMap extract (p:(ps1 ++ ps2))
extractPTermNames (PRefl _ p)        = extract p
extractPTermNames (PEq _ _ _ p1 p2)  = concatMap extract [p1, p2]
extractPTermNames (PRewrite _ a b m) | Just c <- m =
                                       concatMap extract [a, b, c]
extractPTermNames (PRewrite _ a b _) = concatMap extract [a, b]
extractPTermNames (PPair _ _ p1 p2)  = concatMap extract [p1, p2]
extractPTermNames (PDPair _ _ a b c) = concatMap extract [a, b, c]
extractPTermNames (PAlternative _ l) = concatMap extract l
extractPTermNames (PHidden p)        = extract p
extractPTermNames (PGoal _ p1 n p2)  = n : concatMap extract [p1, p2]
extractPTermNames (PDoBlock pdos)    = concatMap extractPDo pdos
extractPTermNames (PIdiom _ p)       = extract p
extractPTermNames (PMetavar n)       = [n]
extractPTermNames (PProof tacts)     = concatMap extractPTactic tacts
extractPTermNames (PTactics tacts)   = concatMap extractPTactic tacts
extractPTermNames (PCoerced p)       = extract p
extractPTermNames (PDisamb _ p)      = extract p
extractPTermNames (PUnifyLog p)      = extract p
extractPTermNames (PNoImplicits p)   = extract p
extractPTermNames _                  = []

-- | Shorter name for extractPTermNames
extract :: PTerm  -- ^ Where to extract names from
        -> [Name] -- ^ Extracted names
extract                               = extractPTermNames

-- | Helper function for extractPTermNames
extractPArg :: PArg -> [Name]
extractPArg (PImp {pname=n, getTm=p}) = n : extract p
extractPArg (PExp {getTm=p})          = extract p
extractPArg (PConstraint {getTm=p})   = extract p
extractPArg (PTacImplicit {pname=n, getScript=p1, getTm=p2})
                                      = n : (concatMap extract [p1, p2])

-- | Helper function for extractPTermNames
extractPDo :: PDo -> [Name]
extractPDo (DoExp   _ p)        = extract p
extractPDo (DoBind  _ n p)      = n : extract p
extractPDo (DoBindP _ p1 p2 ps) = let (ps1, ps2) = unzip ps
                                      ps'        = ps1 ++ ps2
                                  in  concatMap extract (p1 : p2 : ps')
extractPDo (DoLet   _ n p1 p2)  = n : concatMap extract [p1, p2]
extractPDo (DoLetP  _ p1 p2)    = concatMap extract [p1, p2]

-- | Helper function for extractPTermNames
extractPTactic :: PTactic -> [Name]
extractPTactic (Intro ns)         = ns
extractPTactic (Focus n)          = [n]
extractPTactic (Refine n _)       = [n]
extractPTactic (Rewrite p)        = extract p
extractPTactic (Induction p)      = extract p
extractPTactic (CaseTac p)        = extract p
extractPTactic (Equiv p)          = extract p
extractPTactic (MatchRefine n)    = [n]
extractPTactic (LetTac n p)       = n : extract p
extractPTactic (LetTacTy n p1 p2) = n : concatMap extract [p1, p2]
extractPTactic (Exact p)          = extract p
extractPTactic (ProofSearch _ _ _ m ns) | Just n <- m = n : ns
extractPTactic (ProofSearch _ _ _ _ ns) = ns
extractPTactic (Try t1 t2)        = concatMap extractPTactic [t1, t2]
extractPTactic (TSeq t1 t2)       = concatMap extractPTactic [t1, t2]
extractPTactic (ApplyTactic p)    = extract p
extractPTactic (ByReflection p)   = extract p
extractPTactic (Reflect p)        = extract p
extractPTactic (Fill p)           = extract p
extractPTactic (GoalType _ t)     = extractPTactic t
extractPTactic (TCheck p)         = extract p
extractPTactic (TEval p)          = extract p
extractPTactic _                  = []

-- ------------------------------------------------------- [ HTML Generation ]

-- | Generates the actual HTML output based on info from a NsDict
--   A merge of the new docs and any existing docs located in the output dir
--   is attempted.
--   TODO: Ensure the merge always succeeds.
--         Currently the content of 'docs/<builtins>.html' may change between
--         runs, thus not always containing all items referred from other
--         namespace .html files.
createDocs :: IState -- ^ Needed to determine the types of names
           -> NsDict   -- ^ All info from which to generate docs
           -> FilePath -- ^ The base directory to which
                       --   documentation will be written.
           -> IO (Failable ())
createDocs ist nsd out =
  do new                <- not `fmap` (doesFileExist $ out </> "IdrisDoc")
     existing_nss       <- existingNamespaces out
     let nss             = S.union (M.keysSet nsd) existing_nss
     dExists            <- doesDirectoryExist out
     if new && dExists then err $ "Output directory (" ++ out ++ ") is" ++
                                  " already in use for other than IdrisDoc."
       else do
         createDirectoryIfMissing True out
         foldl docGen (return ()) (M.toList nsd)
         createIndex nss out
         -- Create an empty IdrisDoc file to signal 'out' is used for IdrisDoc
         if new -- But only if it not already existed...
            then withFile (out </> "IdrisDoc") WriteMode ((flip hPutStr) "")
            else return ()
         copyDependencies out
         return $ Right ()

  where docGen io (n, c) = do io; createNsDoc ist n c out


-- | (Over)writes the 'index.html' file in the given directory with
--   an (updated) index of namespaces in the documentation
createIndex :: S.Set NsName -- ^ Set of namespace names to
                            --   include in the index
            -> FilePath     -- ^ The base directory to which
                            --   documentation will be written.
            -> IO ()
createIndex nss out =
  do (path, h) <- openTempFile out "index.html"
     BS2.hPut h $ renderHtml $ wrapper Nothing $ do
       H.h1 $ "Namespaces"
       H.ul ! class_ "names" $ do
         let path ns  = "docs" </> genRelNsPath ns "html" 
             item ns  = do let n    = toHtml $ nsName2Str ns
                               link = toValue $ path ns
                           H.li $ H.a ! href link ! class_ "code" $ n
             sort     = L.sortBy (\n1 n2 -> reverse n1 `compare` reverse n2)
         forM_ (sort $ S.toList nss) item
     hClose h
     renameFile path (out </> "index.html")


-- | Generates a HTML file for a namespace and its contents.
--   The location for e.g. Prelude.Algebra is <base>/Prelude/Algebra.html
createNsDoc :: IState   -- ^ Needed to determine the types of names
            -> NsName   -- ^ The name of the namespace to
                        --   create documentation for
            -> NsInfo   -- ^ The contents of the namespace
            -> FilePath -- ^ The base directory to which
                        --   documentation will be written.
            -> IO ()
createNsDoc ist ns content out =
  do let tpath                   = out </> "docs" </> (genRelNsPath ns "html")
         dir                     = takeDirectory tpath
         file                    = takeFileName tpath 
         haveDocs (_, Just d, _) = [d]
         haveDocs _              = []
                                 -- We cannot do anything without a Doc
         content'                = concatMap haveDocs content
     createDirectoryIfMissing True dir
     (path, h) <- openTempFile dir file
     BS2.hPut h $ renderHtml $ wrapper (Just ns) $ do
       H.h1 $ toHtml (nsName2Str ns)
       H.dl ! class_ "decls" $ forM_ content' (createOtherDoc ist)
     hClose h
     renameFile path tpath


-- | Generates a relative filepath for a namespace, appending an extension
genRelNsPath :: NsName   -- ^ Namespace to generate a path for
             -> String   -- ^ Extension suffix
             -> FilePath
genRelNsPath ns suffix = nsName2Str ns <.> suffix


-- | Generates a HTML type signature with proper tags
--   TODO: Turn docstrings into title attributes more robustly
genTypeHeader :: IState -- ^ Needed to determine the types of names
              -> FunDoc -- ^ Type to generate type declaration for
              -> H.Html -- ^ Resulting HTML
genTypeHeader ist (FD n _ args ftype _) = do
  H.span ! class_ (toValue $ "name " ++ getType n)
         ! title  (toValue $ show n)
         $ toHtml $ name $ nsroot n
  H.span ! class_ "word"     $ do nbsp; ":"; nbsp
  H.span ! class_ "signature" $ preEscapedToHtml htmlSignature

  where
        htmlSignature  = displayDecorated decorator $ renderCompact signature
        signature      = pprintPTerm defaultPPOption [] names (idris_infixes ist) ftype
        names          = [ n | (n@(UN n'), _, _, _) <- args,
                           not (T.isPrefixOf (txt "__") n') ]

        decorator (AnnConst c) str | constIsType c = htmlSpan str "type" str
                                   | otherwise     = htmlSpan str "data" str
        decorator (AnnData _ _) str = htmlSpan str "data"    str
        decorator (AnnType _ _)   str = htmlSpan str "type"    str
        decorator AnnKeyword    str = htmlSpan ""  "keyword" str
        decorator (AnnBoundName n i) str | Just t <- M.lookup n docs =
          let cs = (if i then "implicit " else "") ++ "documented boundvar"
          in  htmlSpan t cs str
        decorator (AnnBoundName _ i) str =
          let cs = (if i then "implicit " else "") ++ "boundvar"
          in  htmlSpan "" cs str
        decorator (AnnName n _ _ _) str
          | filterName n = htmlLink (show n) (getType n) (link n) str
          | otherwise    = htmlSpan ""       (getType n)          str
        decorator (AnnTextFmt BoldText)      str = "<b>" ++ str ++ "</b>"
        decorator (AnnTextFmt UnderlineText) str = "<u>" ++ str ++ "</u>"
        decorator (AnnTextFmt ItalicText)    str = "<i>" ++ str ++ "</i>"
        decorator _ str = str

        htmlSpan :: String -> String -> String -> String
        htmlSpan t cs str = do
          R.renderHtml $ H.span ! class_ (toValue cs)
                                ! title (toValue t)
                                $ toHtml str
        htmlLink :: String -> String -> String -> String -> String
        htmlLink t cs a str = do
          R.renderHtml $ H.a ! class_ (toValue cs)
                       ! title (toValue t) ! href (toValue a)
                       $ toHtml str

        docs           = M.fromList $ mapMaybe docExtractor args
        docExtractor (_, _, _, Nothing) = Nothing
        docExtractor (n, _, _, Just d)  = Just (n, doc2Str d)
                         -- TODO: Remove <p> tags more robustly
        doc2Str d      = let dirty = renderMarkup $ contents $ renderDoc $ d
                         in  take (length dirty - 8) $ drop 3 dirty

        name (NS n ns) = show (NS (sUN $ name n) ns)
        name n         = let n' = show n
                         in  if (head n') `elem` opChars
                                then '(':(n' ++ ")")
                                else n'

        link n         = let path = genRelNsPath (getNs n) "html"
                         in  path ++ "#" ++ (show n)

        getType :: Name -> String
        getType n      = let ctxt = tt_ctxt ist
                         in  case () of
                               _ | isDConName n ctxt -> "constructor"
                               _ | isFnName   n ctxt -> "function"
                               _ | isTConName n ctxt -> "type"
                               _ | otherwise         -> ""

-- | Generates HTML documentation for a function.
createFunDoc :: IState -- ^ Needed to determine the types of names
             -> FunDoc -- ^ Function to generate block for
             -> H.Html -- ^ Resulting HTML
createFunDoc ist fd@(FD name docstring args ftype fixity) = do
  H.dt ! (A.id $ toValue $ show name) $ genTypeHeader ist fd
  H.dd $ do
    (if nullDocstring docstring then Empty else renderDoc docstring)
    let args'             = filter (\(_, _, _, d) -> isJust d) args
    if (not $ null args') || (isJust fixity)
       then H.dl $ do
         if (isJust fixity) then do
             H.dt ! class_ "fixity" $ "Fixity"
             let f = fromJust fixity
             H.dd ! class_ "fixity" ! title (toValue $ show f) $ genFix f
           else Empty
         forM_ args' genArg
       else Empty

  where genFix (Infixl {prec=p})  =
          toHtml $ "Left associative, precedence " ++ show p
        genFix (Infixr {prec=p})  =
          toHtml $ "Left associative, precedence " ++ show p
        genFix (InfixN {prec=p})  =
          toHtml $ "Non-associative, precedence " ++ show p
        genFix (PrefixN {prec=p}) =
          toHtml $ "Prefix, precedence " ++ show p
        genArg (_, _, _, Nothing)           = Empty
        genArg (name, _, _, Just docstring) = do
          H.dt $ toHtml $ show name
          H.dd $ renderDoc docstring


-- | Generates HTML documentation for any Docs type
--   TODO: Generate actual signatures for typeclasses
createOtherDoc :: IState -- ^ Needed to determine the types of names
               -> Docs   -- ^ Namespace item to generate HTML block for
               -> H.Html -- ^ Resulting HTML
createOtherDoc ist (FunDoc fd)                = createFunDoc ist fd

createOtherDoc ist (ClassDoc n docstring fds _ _ _) = do
  H.dt ! (A.id $ toValue $ show n) $ do
    H.span ! class_ "word" $ do "class"; nbsp
    H.span ! class_ "name type"
           ! title  (toValue $ show n)
           $ toHtml $ name $ nsroot n
    H.span ! class_ "signature" $ nbsp
  H.dd $ do
    (if nullDocstring docstring then Empty else renderDoc docstring)
    H.dl ! class_ "decls" $ forM_ fds (createFunDoc ist)

  where name (NS n ns) = show (NS (sUN $ name n) ns)
        name n         = let n' = show n
                         in  if (head n') `elem` opChars
                                then '(':(n' ++ ")")
                                else n'

createOtherDoc ist (DataDoc fd@(FD n docstring args _ _) fds) = do
  H.dt ! (A.id $ toValue $ show n) $ do
    H.span ! class_ "word" $ do "data"; nbsp
    genTypeHeader ist fd
  H.dd $ do
    (if nullDocstring docstring then Empty else renderDoc docstring)
    let args' = filter (\(_, _, _, d) -> isJust d) args
    if not $ null args'
       then H.dl $ forM_ args' genArg
       else Empty
    H.dl ! class_ "decls" $ forM_ fds (createFunDoc ist)

  where genArg (_, _, _, Nothing)           = Empty
        genArg (name, _, _, Just docstring) = do
          H.dt $ toHtml $ show name
          H.dd $ renderDoc docstring


-- | Generates everything but the actual content of the page
wrapper :: Maybe NsName -- ^ Namespace name, unless it is the index
        -> H.Html         -- ^ Inner HTML
        -> H.Html
wrapper ns inner =
  let (index, str) = extract ns
      base       = if index then "" else "../"
      styles     = base ++ "styles.css" :: String
      indexPage  = base ++ "index.html" :: String
  in  H.docTypeHtml $ do
    H.head $ do
      H.title $ do
        "IdrisDoc"
        if index then " Index" else do
          ": "
          toHtml str
      H.link ! type_ "text/css" ! rel "stylesheet"
             ! href (toValue styles)
    H.body ! class_ (if index then "index" else "namespace") $ do
      H.div ! class_ "wrapper" $ do
        H.header $ do
          H.strong "IdrisDoc"
          if index then Empty else do
            ": "
            toHtml str
          H.nav $ H.a ! href (toValue indexPage) $ "Index"
        H.div ! class_ "container" $ inner
      H.footer $ do
        "Produced by IdrisDoc version "
        toHtml version

  where extract (Just ns) = (False, nsName2Str ns)
        extract _         = (True,  "")


-- | Non-break space character
nbsp :: H.Html
nbsp = preEscapedToHtml ("&nbsp;" :: String)


-- | Returns a list of namespaces already documented in a IdrisDoc directory
existingNamespaces :: FilePath -- ^ The base directory containing the
                               --   'docs' directory with existing
                               --   namespace pages
                   -> IO (S.Set NsName)
existingNamespaces out = do
  let docs     = out </> "docs"
      str2Ns s | s == rootNsStr = []
      str2Ns s = reverse $ T.splitOn (T.singleton '.') (txt s)
      toNs  fp = do isFile    <- doesFileExist $ docs </> fp
                    let isHtml = ".html" == takeExtension fp
                        name   = dropExtension fp
                        ns     = str2Ns name
                    return $ if isFile && isHtml then Just ns else Nothing
  docsExists  <- doesDirectoryExist docs
  if not docsExists
     then    return S.empty
     else do contents    <- getDirectoryContents docs
             namespaces  <- catMaybes `fmap` (sequence $ map toNs contents)
             return $ S.fromList namespaces


-- | Copies IdrisDoc dependencies such as stylesheets to a directory
copyDependencies :: FilePath -- ^ The base directory to which
                             --   dependencies should be written
                 -> IO ()
copyDependencies dir =
  do styles <- getDataFileName $ "idrisdoc" </> "styles.css"
     copyFile styles (dir </> "styles.css")

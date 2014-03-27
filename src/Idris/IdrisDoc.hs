{-# LANGUAGE PatternGuards #-}

-- | Generation of HTML documentation for Idris code
module Idris.IdrisDoc (generateDocs) where

import Idris.Core.TT (Name (..))
import Idris.Core.Evaluate (ctxtAlist, Def (..))
import Idris.AbsSyntax (IState, tt_ctxt, runIO, imported)

import qualified Data.Map as M
import qualified Data.Text as T


-- | Generates HTML documentation for a series of loaded namespaces and their dependencies.
generateDocs :: IState -- ^ IState where all necessary information is extracted from.
             -> [Name] -- ^ List of namespaces to generate documentation for.
             -> FilePath -- ^ The directory to which documentation will be written.
             -> IO (Either String ())
generateDocs ist nss out = -- err "IdrisDoc is still in development..."
                           -- Right `fmap` (print $ createNameTrie ist)
                           -- Right `fmap` (print $ imported ist)


type Failable = Either String
type NsDict   = M.Map Name NsInfo

data NsInfo   = NsInfo { ns :: Name, info :: Maybe () }

-- | Make an error message
err :: String -> IO (Failable ())
err s = return $ Left s


-- ------------------------------------------------------------- [ Name Trie ]

-- | A NameTrie is either:
--   a namespace item,
--   a namespace node with children,
--   both
data NameTrie a = NameTrie {
                             content  :: Maybe (Name, a),
                             children :: M.Map T.Text (NameTrie a)
                           } deriving Show

-- | Empty NameTrie
ntEmpty :: NameTrie a
ntEmpty = NameTrie { content = Nothing, children = M.empty }

-- | Build NameTrie from a Map
ntFromMap :: M.Map T.Text (NameTrie a) -- ^ Mapping of namespace contents
          -> NameTrie a
ntFromMap m = NameTrie { content = Nothing, children = m }

-- | Build NameTrie from a (Maybe NameTrie a)
ntFromMaybe :: Maybe (NameTrie a) -- ^ Maybe a NameTrie?
            -> NameTrie a
ntFromMaybe (Just nt) = nt
ntFromMaybe Nothing   = ntEmpty


-- | Lookup a sub-NameTrie based on a NameTrie identifier.
--   Identifier example: A.B.c -> [A,B,c]    (reverse Idris-style)
ntLookup :: [T.Text]           -- ^ Identifier to lookup
         -> NameTrie a         -- ^ The trie to lookup within
         -> Maybe (NameTrie a)
ntLookup (t:ts) n | Just n' <- M.lookup t (children n) = ntLookup ts n'
ntLookup [t]    n = M.lookup t (children n)
ntLookup _      _ = Nothing


-- | Add content to a NameTrie
ntInsert :: Name       -- ^ The name to add content under
         -> a          -- ^ The content to add
         -> NameTrie a -- ^ The NameTrie (Ns) to add the content to
         -> NameTrie a
ntInsert n@(UN t)         c = ntInsertHelper [t]              n c
ntInsert n@(NS (UN t) ns) c = ntInsertHelper (reverse $ t:ns) n c
ntInsert _                _ = id   -- Ignore

-- | Add content to a NameTrie using a NameTrie identifier
ntInsertHelper :: [T.Text]   -- ^ Path of identifiers
               -> Name       -- ^ Name of final entry
               -> a          -- ^ The content to add
               -> NameTrie a -- ^ The NameTrie (Ns) to add the content to
               -> NameTrie a
ntInsertHelper (t:ts) n c nt = let cs    = children nt
                                   subnt = ntFromMaybe $ M.lookup t cs
                                   nt'   = ntInsertHelper ts n c subnt
                               in  nt { children = M.insert t nt' cs }
ntInsertHelper []     n c nt = nt { content = Just (n, c) }


-- | Creates a trie on which names can be looked up by traveling their namespaces
ntCreate :: IState       -- ^ IState to fetch info from
         -> NameTrie Def
ntCreate ist = let defList        = ctxtAlist $ tt_ctxt ist
                   adder t (n, d) = ntInsert n d t
               in  foldl adder ntEmpty defList
                         

-- --------------------------------------------------------- [ Info Fetching ]

-- | Fetch info about namespaces and their contents
fetchInfo :: IState -- ^ IState to fetch info from
          -> [Name] -- ^ List of namespaces to fetch info for
          -> NsDict -- ^ Mapping from namespace name to info about its contents
fetchInfo ist ns = let nameTrie = ntCreate ist
                   in  undefined

-- | Returns all names defined in a namespace, including child namespaces
allNamesInNs :: NameTrie a -- ^ NameTrie to fetch info from
             -> Name       -- ^ 
             -> [Name]     -- ^ All names within the namespace
allNamesInNs nt n = undefined

-- | Returns the namespace within a name is defined
nsOfName :: Name   -- ^ Name to retrieve the namespace of
         -> Name   -- ^ The namespace
nsOfName n = undefined

-- ------------------------------------------------------- [ HTML Generation ]
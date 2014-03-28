{-# LANGUAGE PatternGuards #-}

-- | Generation of HTML documentation for Idris code
module Idris.IdrisDoc (generateDocs) where

import Idris.Core.TT (Name (..), txt, nsroot)
import Idris.Core.Evaluate (ctxtAlist, Def (..))
import Idris.AbsSyntax (IState, tt_ctxt, imported)

import qualified Data.Map as M
import qualified Data.Text as T

-- ---------------------------------------------------------------- [ Public ]

-- | Generates HTML documentation for a series of loaded namespaces and their dependencies.
generateDocs :: IState -- ^ IState where all necessary information is extracted from.
             -> [Name] -- ^ List of namespaces to generate documentation for.
             -> FilePath -- ^ The directory to which documentation will be written.
             -> IO (Either String ())
generateDocs ist nss out = -- err "IdrisDoc is still in development..."
                           -- Right `fmap` (print $ map toNsName nss)
                           -- Right `fmap` (print $ nsDict ist)
                            Right `fmap` (print $ imported ist)


-- ----------------------------------------------------------------- [ Types ]

type Failable = Either String
type NsName   = [T.Text]
type NsInfo   = [(Name, Def)]
type NsDict   = M.Map NsName NsInfo

-- --------------------------------------------------------------- [ Utility ]

-- | Make an error message
err :: String -> IO (Failable ())
err s = return $ Left s


-- | Converts a Name into a [Text] corresponding to the namespace part of a NS Name
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

-- --------------------------------------------------------- [ Info Fetching ]

-- | Fetch info about namespaces and their contents
fetchInfo :: IState -- ^ IState to fetch info from
          -> [Name] -- ^ List of namespaces to fetch info for
          -> NsDict -- ^ Mapping from namespace name to info about its contents
fetchInfo ist ns = let nsMap = nsDict ist
                   in  undefined


-- | Returns a map of NsName -> [(Name, Def)]
nsDict :: IState
       -> NsDict
nsDict ist = let nameDefList      = ctxtAlist $ tt_ctxt ist
                 adder m c@(n, d) = M.insertWith (++) (getNs n) [c] m
             in  foldl adder M.empty nameDefList

-- ------------------------------------------------------- [ HTML Generation ]


{-|
Module      : Idris.REPL.Browse
Description : Browse the current namespace.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns -fwarn-unused-imports #-}

module Idris.REPL.Browse (namespacesInNS, namesInNS) where

import Idris.AbsSyntax (getContext)
import Idris.AbsSyntaxTree (Idris)
import Idris.Core.Evaluate (Accessibility(Hidden, Private), ctxtAlist,
                            lookupDefAccExact)
import Idris.Core.TT (Name(..))

import Control.Monad (filterM)
import Data.List (isSuffixOf, nub)
import Data.Maybe (mapMaybe)
import qualified Data.Text as T (unpack)

-- | Find the sub-namespaces of a given namespace. The components
-- should be in display order rather than the order that they are in
-- inside of NS constructors.
namespacesInNS :: [String] -> Idris [[String]]
namespacesInNS ns = do let revNS = reverse ns
                       allNames <- fmap ctxtAlist getContext
                       return . nub $
                         [ reverse space | space <- mapMaybe (getNS . fst) allNames
                                         , revNS `isSuffixOf` space
                                         , revNS /= space ]
  where getNS (NS _ namespace) = Just (map T.unpack namespace)
        getNS _ = Nothing

-- | Find the user-accessible names that occur directly within a given
-- namespace. The components should be in display order rather than
-- the order that they are in inside of NS constructors.
namesInNS :: [String] -> Idris [Name]
namesInNS ns = do let revNS = reverse ns
                  allNames <- fmap ctxtAlist getContext
                  let namesInSpace = [ n | (n, space) <- mapMaybe (getNS . fst) allNames
                                         , revNS == space ]
                  filterM accessible namesInSpace
  where getNS n@(NS (UN n') namespace) = Just (n, (map T.unpack namespace))
        getNS _ = Nothing
        accessible n = do ctxt <- getContext
                          case lookupDefAccExact n False ctxt of
                            Just (_, Hidden ) -> return False
                            Just (_, Private ) -> return False
                            _ -> return True

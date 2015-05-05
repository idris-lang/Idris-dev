{-# OPTIONS_GHC -fwarn-incomplete-patterns -fwarn-unused-imports #-}

module Idris.REPL.Browse (namespacesInNS, namesInNS) where

import Data.List (isSuffixOf, nub)
import Data.Maybe (mapMaybe)
import qualified Data.Text as T (unpack)

import Idris.Core.Evaluate (ctxtAlist)
import Idris.Core.TT (Name(..))

import Idris.AbsSyntaxTree (Idris)
import Idris.AbsSyntax (getContext)

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
                  return [ n | (n, space) <- mapMaybe (getNS . fst) allNames
                             , revNS == space ]
  where getNS n@(NS (UN n') namespace) = Just (n, (map T.unpack namespace))
        getNS _ = Nothing

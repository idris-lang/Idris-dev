{-# LANGUAGE DeriveGeneric #-}
{-|
Module      : IRTS.CodegenCommon
Description : Common data structures required for all code generators.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module IRTS.CodegenCommon where

import Idris.Core.Evaluate
import Idris.Core.TT
import IRTS.Defunctionalise
import IRTS.Simplified

import GHC.Generics (Generic)

data DbgLevel = NONE | DEBUG | TRACE deriving Eq
data OutputType = Raw | Object | Executable deriving (Eq, Show, Generic)

-- | Everything which might be needed in a code generator.
--
-- A CG can choose which level of Decls to generate code from
-- (simplified, defunctionalised or merely lambda lifted) and has
-- access to the list of object files, libraries, etc.

data CodegenInfo = CodegenInfo {
    outputFile    :: String
  , outputType    :: OutputType
  , targetTriple  :: String
  , targetCPU     :: String
  , includes      :: [FilePath]
  , importDirs    :: [FilePath]
  , compileObjs   :: [String]
  , compileLibs   :: [String]
  , compilerFlags :: [String]
  , debugLevel    :: DbgLevel
  , simpleDecls   :: [(Name, SDecl)]
  , defunDecls    :: [(Name, DDecl)]
  , liftDecls     :: [(Name, LDecl)]
  , interfaces    :: Bool
  , exportDecls   :: [ExportIFace]
  , ttDecls       :: [(Name, TTDecl)]
  }

type CodeGenerator = CodegenInfo -> IO ()

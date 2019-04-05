{-|
Module      : Idris.Options
Description : Compiler options for Idris.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, DeriveGeneric, PatternGuards #-}

module Idris.Options (Codegen(..), ConsoleWidth(..), HowMuchDocs(..), IRFormat(..),
                      LanguageExt(..), LogCat(..), Opt(..), Optimisation(..),
                      OutputFmt(..), REPLPort(..), codegenCats, elabCats, getBC,
                      getClient, getCodegen, getCodegenArgs, getColour, getConsoleWidth,
                      getEvalExpr, getExecScript, getFile, getIBCSubDir, getImportDir,
                      getLanguageExt, getOptLevel, getOptimisation, getOutput,
                      getOutputTy, getPkg, getPkgCheck, getPkgClean, getPkgDir,
                      getPkgIndex, getPkgMkDoc, getPkgREPL, getPkgTest, getPort,
                      getSourceDir, loggingCatsStr, opt, parserCats, strLogCat) where

import Data.Maybe
import GHC.Generics (Generic)
import IRTS.CodegenCommon (OutputType)
import Network.Socket (PortNumber)

data Opt = Filename String
         | Quiet
         | NoBanner
         | ColourREPL Bool
         | Idemode
         | IdemodeSocket
         | IndentWith Int
         | IndentClause Int
         | ShowAll
         | ShowLibs
         | ShowLibDir
         | ShowDocDir
         | ShowIncs
         | ShowPkgs
         | ShowLoggingCats
         | NoBasePkgs
         | NoPrelude
         | NoBuiltins -- only for the really primitive stuff!
         | NoREPL
         | OLogging Int
         | OLogCats [LogCat]
         | Output String
         | Interface
         | TypeCase
         | TypeInType
         | DefaultTotal
         | DefaultPartial
         | WarnPartial
         | WarnReach
         | AuditIPkg
         | EvalTypes
         | NoCoverage
         | ErrContext
         | ShowImpl
         | Verbose Int
         | Port REPLPort -- ^ REPL TCP port
         | IBCSubDir String
         | ImportDir String
         | SourceDir String
         | PkgBuild String
         | PkgInstall String
         | PkgClean String
         | PkgCheck String
         | PkgREPL String
         | PkgDocBuild String -- IdrisDoc
         | PkgDocInstall String
         | PkgTest String
         | PkgIndex FilePath
         | WarnOnly
         | Pkg String
         | BCAsm String
         | DumpDefun String
         | DumpCases String
         | UseCodegen Codegen
         | CodegenArgs String
         | OutputTy OutputType
         | Extension LanguageExt
         | InterpretScript String
         | EvalExpr String
         | TargetTriple String
         | TargetCPU String
         | OptLevel Int
         | AddOpt Optimisation
         | RemoveOpt Optimisation
         | Client String
         | ShowOrigErr
         | AutoWidth -- ^ Automatically adjust terminal width
         | AutoSolve -- ^ Automatically issue "solve" tactic in old-style interactive prover
         | UseConsoleWidth ConsoleWidth
         | DumpHighlights
         | DesugarNats
         | NoOldTacticDeprecationWarnings -- ^ Don't show deprecation warnings for old-style tactics
         | AllowCapitalizedPatternVariables -- ^ Allow pattern variables to be capitalized
    deriving (Show, Eq, Generic)


data REPLPort = DontListen | ListenPort PortNumber
  deriving (Eq, Generic, Show)


data Codegen = Via IRFormat String
             | Bytecode
    deriving (Show, Eq, Generic)


data LanguageExt = TypeProviders | ErrorReflection | UniquenessTypes
                 | DSLNotation   | ElabReflection  | FCReflection
                 | LinearTypes
  deriving (Show, Eq, Read, Ord, Generic)

data IRFormat = IBCFormat | JSONFormat deriving (Show, Eq, Generic)


-- | How wide is the console?
data ConsoleWidth = InfinitelyWide -- ^ Have pretty-printer assume that lines should not be broken
                  | ColsWide Int   -- ^ Manually specified - must be positive
                  | AutomaticWidth -- ^ Attempt to determine width, or 80 otherwise
   deriving (Show, Eq, Generic)

data HowMuchDocs = FullDocs | OverviewDocs

data OutputFmt = HTMLOutput | LaTeXOutput

data Optimisation = PETransform | GeneralisedNatHack -- ^ partial eval and associated transforms
  deriving (Show, Eq, Generic)

-- | Recognised logging categories for the Idris compiler.
--
-- @TODO add in sub categories.
data LogCat = IParse
            | IElab
            | ICodeGen
            | IErasure
            | ICoverage
            | IIBC
            deriving (Show, Eq, Ord, Generic)

strLogCat :: LogCat -> String
strLogCat IParse    = "parser"
strLogCat IElab     = "elab"
strLogCat ICodeGen  = "codegen"
strLogCat IErasure  = "erasure"
strLogCat ICoverage = "coverage"
strLogCat IIBC      = "ibc"

codegenCats :: [LogCat]
codegenCats =  [ICodeGen]

parserCats :: [LogCat]
parserCats = [IParse]

elabCats :: [LogCat]
elabCats = [IElab]

loggingCatsStr :: String
loggingCatsStr = unlines
    [ (strLogCat IParse)
    , (strLogCat IElab)
    , (strLogCat ICodeGen)
    , (strLogCat IErasure)
    , (strLogCat ICoverage)
    , (strLogCat IIBC)
    ]

getFile :: Opt -> Maybe String
getFile (Filename s) = Just s
getFile _ = Nothing

getBC :: Opt -> Maybe String
getBC (BCAsm s) = Just s
getBC _ = Nothing

getOutput :: Opt -> Maybe String
getOutput (Output s) = Just s
getOutput _ = Nothing

getIBCSubDir :: Opt -> Maybe String
getIBCSubDir (IBCSubDir s) = Just s
getIBCSubDir _ = Nothing

getImportDir :: Opt -> Maybe String
getImportDir (ImportDir s) = Just s
getImportDir _ = Nothing

getSourceDir :: Opt -> Maybe String
getSourceDir (SourceDir s) = Just s
getSourceDir _ = Nothing

getPkgDir :: Opt -> Maybe String
getPkgDir (Pkg s) = Just s
getPkgDir _ = Nothing

getPkg :: Opt -> Maybe (Bool, String)
getPkg (PkgBuild s)   = Just (False, s)
getPkg (PkgInstall s) = Just (True, s)
getPkg _ = Nothing

getPkgClean :: Opt -> Maybe String
getPkgClean (PkgClean s) = Just s
getPkgClean _ = Nothing

getPkgREPL :: Opt -> Maybe String
getPkgREPL (PkgREPL s) = Just s
getPkgREPL _ = Nothing

getPkgCheck :: Opt -> Maybe String
getPkgCheck (PkgCheck s) = Just s
getPkgCheck _              = Nothing

-- | Returns None if given an Opt which is not PkgMkDoc
--   Otherwise returns Just x, where x is the contents of PkgMkDoc
getPkgMkDoc :: Opt                  -- ^ Opt to extract
            -> Maybe (Bool, String) -- ^ Result
getPkgMkDoc (PkgDocBuild  str)  = Just (False,str)
getPkgMkDoc (PkgDocInstall str) = Just (True,str)
getPkgMkDoc _              = Nothing

getPkgTest :: Opt          -- ^ the option to extract
           -> Maybe String -- ^ the package file to test
getPkgTest (PkgTest f) = Just f
getPkgTest _ = Nothing

getCodegen :: Opt -> Maybe Codegen
getCodegen (UseCodegen x) = Just x
getCodegen _ = Nothing

getCodegenArgs :: Opt -> Maybe String
getCodegenArgs (CodegenArgs args) = Just args
getCodegenArgs _ = Nothing

getConsoleWidth :: Opt -> Maybe ConsoleWidth
getConsoleWidth (UseConsoleWidth x) = Just x
getConsoleWidth _ = Nothing

getExecScript :: Opt -> Maybe String
getExecScript (InterpretScript expr) = Just expr
getExecScript _ = Nothing

getPkgIndex :: Opt -> Maybe FilePath
getPkgIndex (PkgIndex file) = Just file
getPkgIndex _ = Nothing

getEvalExpr :: Opt -> Maybe String
getEvalExpr (EvalExpr expr) = Just expr
getEvalExpr _ = Nothing

getOutputTy :: Opt -> Maybe OutputType
getOutputTy (OutputTy t) = Just t
getOutputTy _ = Nothing

getLanguageExt :: Opt -> Maybe LanguageExt
getLanguageExt (Extension e) = Just e
getLanguageExt _ = Nothing

getTriple :: Opt -> Maybe String
getTriple (TargetTriple x) = Just x
getTriple _ = Nothing

getCPU :: Opt -> Maybe String
getCPU (TargetCPU x) = Just x
getCPU _ = Nothing

getOptLevel :: Opt -> Maybe Int
getOptLevel (OptLevel x) = Just x
getOptLevel _ = Nothing

getOptimisation :: Opt -> Maybe (Bool,Optimisation)
getOptimisation (AddOpt p)    = Just (True,  p)
getOptimisation (RemoveOpt p) = Just (False, p)
getOptimisation _             = Nothing

getColour :: Opt -> Maybe Bool
getColour (ColourREPL b) = Just b
getColour _ = Nothing

getClient :: Opt -> Maybe String
getClient (Client x) = Just x
getClient _ = Nothing

-- Get the first valid port
getPort :: [Opt] -> Maybe REPLPort
getPort []            = Nothing
getPort (Port p : _ ) = Just p
getPort (_      : xs) = getPort xs

opt :: (Opt -> Maybe a) -> [Opt] -> [a]
opt = mapMaybe

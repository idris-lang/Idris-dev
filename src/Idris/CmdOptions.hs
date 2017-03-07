{-# LANGUAGE CPP #-}
{-|
Module      : Idris.CmdOptions
Description : A parser for the CmdOptions for the Idris executable.
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE Arrows #-}

module Idris.CmdOptions
  (
    module Idris.CmdOptions
  , opt
  , getClient, getPkg, getPkgCheck, getPkgClean, getPkgMkDoc
  , getPkgREPL, getPkgTest, getPort, getIBCSubDir
  ) where

import Idris.AbsSyntax (getClient, getIBCSubDir, getPkg, getPkgCheck,
                        getPkgClean, getPkgMkDoc, getPkgREPL, getPkgTest,
                        getPort, opt)
import Idris.AbsSyntaxTree
import Idris.Info (getIdrisVersion)
import IRTS.CodegenCommon

import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (throwE)
import Control.Monad.Trans.Reader (ask)
import Data.Char
import Data.Maybe
#if MIN_VERSION_optparse_applicative(0,13,0)
import Data.Monoid ((<>))
#endif
import Options.Applicative
import Options.Applicative.Arrows
import Options.Applicative.Types (ReadM(..))

import Text.ParserCombinators.ReadP hiding (many, option)

import Safe (lastMay)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

runArgParser :: IO [Opt]
runArgParser = do opts <- execParser $ info parser
                          (fullDesc
                           <> headerDoc   (Just idrisHeader)
                           <> progDescDoc (Just idrisProgDesc)
                           <> footerDoc   (Just idrisFooter)
                          )
                  return $ preProcOpts opts
               where
                 idrisHeader = PP.hsep [PP.text "Idris version", PP.text getIdrisVersion, PP.text ", (C) The Idris Community 2016"]
                 idrisProgDesc = PP.vsep [PP.empty,
                                          PP.text "Idris is a general purpose pure functional programming language with dependent",
                                          PP.text "types. Dependent types allow types to be predicated on values, meaning that",
                                          PP.text "some aspects of a program's behaviour can be specified precisely in the type.",
                                          PP.text "It is compiled, with eager evaluation. Its features are influenced by Haskell",
                                          PP.text "and ML.",
                                          PP.empty,
                                          PP.vsep $ map (PP.indent 4 . PP.text) [
                                              "+ Full dependent types with dependent pattern matching",
                                              "+ Simple case expressions, where-clauses, with-rule",
                                              "+ Pattern matching let- and lambda-bindings",
                                              "+ Overloading via Interfaces (Type class-like), Monad comprehensions",
                                              "+ do-notation, idiom brackets",
                                              "+ Syntactic conveniences for lists, tuples, dependent pairs",
                                              "+ Totality checking",
                                              "+ Coinductive types",
                                              "+ Indentation significant syntax, Extensible syntax",
                                              "+ Tactic based theorem proving (influenced by Coq)",
                                              "+ Cumulative universes",
                                              "+ Simple Foreign Function Interface",
                                              "+ Hugs style interactive environment"
                                            ]]
                 idrisFooter = PP.vsep [PP.text "It is important to note that Idris is first and foremost a research tool",
                                        PP.text "and project. Thus the tooling provided and resulting programs created",
                                        PP.text "should not necessarily be seen as production ready nor for industrial use.",
                                        PP.empty,
                                        PP.text "More details over Idris can be found online here:",
                                        PP.empty,
                                        PP.indent 4 (PP.text "http://www.idris-lang.org/")]

pureArgParser :: [String] -> [Opt]
pureArgParser args = case getParseResult $ execParserPure (prefs idm) (info parser idm) args of
  Just opts -> preProcOpts opts
  Nothing -> []

parser :: Parser [Opt]
parser = runA $ proc () -> do
  flags <- asA parseFlags -< ()
  files <- asA (many $ argument (fmap Filename str) (metavar "FILES")) -< ()
  A parseVersion >>> A helper -< (flags ++ files)

parseFlags :: Parser [Opt]
parseFlags = many $
      flag' NoBanner (long "nobanner" <> help "Suppress the banner")
  <|> flag' Quiet    (short 'q' <> long "quiet" <> help "Quiet verbosity")

  -- IDE Mode Specific Flags
  <|> flag' Idemode       (long "ide-mode"        <> help "Run the Idris REPL with machine-readable syntax")
  <|> flag' IdemodeSocket (long "ide-mode-socket" <> help "Choose a socket for IDE mode to listen on")

  -- Client flags
  <|> Client <$> strOption (long "client")

  -- Logging Flags
  <|> OLogging <$> option auto (long "log" <> metavar "LEVEL" <> help "Debugging log level")
  <|> OLogCats <$> option (str >>= parseLogCats)
                           (long "logging-categories"
                         <> metavar "CATS"
                         <> help "Colon separated logging categories. Use --listlogcats to see list.")

  -- Turn off things
  <|> flag' NoBasePkgs (long "nobasepkgs" <> help "Do not use the given base package")
  <|> flag' NoPrelude  (long "noprelude"  <> help "Do not use the given prelude")
  <|> flag' NoBuiltins (long "nobuiltins" <> help "Do not use the builtin functions")

  <|> flag' NoREPL     (long "check"      <> help "Typecheck only, don't start the REPL")

  <|> Output <$> strOption (short 'o' <> long "output" <> metavar "FILE" <> help "Specify output file")

  --   <|> flag' TypeCase (long "typecase")
  <|> flag' Interface      (long "interface"   <> help "Generate interface files from ExportLists")
  <|> flag' TypeInType     (long "typeintype"  <> help "Turn off Universe checking")
  <|> flag' DefaultTotal   (long "total"       <> help "Require functions to be total by default")
  <|> flag' DefaultPartial (long "partial")
  <|> flag' WarnPartial    (long "warnpartial" <> help "Warn about undeclared partial functions")
  <|> flag' WarnReach      (long "warnreach"   <> help "Warn about reachable but inaccessible arguments")
  <|> flag' AuditIPkg      (long "warnipkg"    <> help "Warn about possible incorrect package specifications")
  <|> flag' NoCoverage     (long "nocoverage")
  <|> flag' ErrContext     (long "errorcontext")

  -- Show things
  <|> flag' ShowAll         (long "info"        <> help "Display information about installation.")
  <|> flag' ShowLoggingCats (long "listlogcats" <> help "Display logging categories")
  <|> flag' ShowLibs        (long "link"        <> help "Display link flags")
  <|> flag' ShowPkgs        (long "listlibs"    <> help "Display installed libraries")
  <|> flag' ShowLibDir      (long "libdir"      <> help "Display library directory")
  <|> flag' ShowDocDir      (long "docdir"      <> help "Display idrisdoc install directory")
  <|> flag' ShowIncs        (long "include"     <> help "Display the includes flags")

  <|> flag' (Verbose 3) (long "V2" <> help "Loudest verbosity")
  <|> flag' (Verbose 2) (long "V1" <> help "Louder verbosity")
  <|> flag' (Verbose 1) (short 'V' <> long "V0" <>long "verbose" <> help "Loud verbosity")

  <|> IBCSubDir <$> strOption (long "ibcsubdir" <> metavar "FILE" <> help "Write IBC files into sub directory")
  <|> ImportDir <$> strOption (short 'i' <> long "idrispath" <> help "Add directory to the list of import paths")
  <|> SourceDir <$> strOption (long "sourcepath" <> help "Add directory to the list of source search paths")

  <|> flag' WarnOnly (long "warn")

  <|> Pkg  <$> strOption (short 'p' <> long "package" <> help "Add package as a dependency")
  <|> Port <$> option portReader (long "port" <> metavar "PORT" <> help "REPL TCP port - pass \"none\" to not bind any port")

  -- Package commands
  <|> PkgBuild   <$> strOption (long "build"    <> metavar "IPKG" <> help "Build package")
  <|> PkgInstall <$> strOption (long "install"  <> metavar "IPKG" <> help "Install package")
  <|> PkgREPL    <$> strOption (long "repl"     <> metavar "IPKG" <> help "Launch REPL, only for executables")
  <|> PkgClean   <$> strOption (long "clean"    <> metavar "IPKG" <> help "Clean package")
  <|> (PkgDocBuild   <$> strOption (long "mkdoc"      <> metavar "IPKG" <> help "Generate IdrisDoc for package"))
  <|> PkgDocInstall <$> strOption (long "installdoc" <> metavar "IPKG" <> help "Install IdrisDoc for package")
  <|> PkgCheck   <$> strOption (long "checkpkg" <> metavar "IPKG" <> help "Check package only")
  <|> PkgTest    <$> strOption (long "testpkg"  <> metavar "IPKG" <> help "Run tests for package")

  -- Interactive Editing Flags
  <|> IndentWith    <$> option auto (long "indent-with"
                                           <> metavar "INDENT"
                                           <> help "Indentation to use with :makewith (default 2)")
  <|> IndentClause  <$> option auto (long "indent-clause"
                                           <> metavar "INDENT"
                                           <> help "Indentation to use with :addclause (default 2)")

  -- Misc options
  <|> BCAsm <$> strOption (long "bytecode")

  <|> flag' (OutputTy Raw)          (short 'S' <> long "codegenonly" <> help "Do no further compilation of code generator output")
  <|> flag' (OutputTy Object)       (short 'c' <> long "compileonly" <> help "Compile to object files rather than an executable")

  <|> DumpDefun <$> strOption (long "dumpdefuns")
  <|> DumpCases <$> strOption (long "dumpcases")

  <|> (UseCodegen . parseCodegen) <$> strOption (long "codegen"
                                              <> metavar "TARGET"
                                              <> help "Select code generator: C, Javascript, Node and bytecode are bundled with Idris")

  <|> ((UseCodegen . Via JSONFormat) <$> strOption (long "portable-codegen"
                                                 <> metavar "TARGET"
                                                 <> help "Pass the name of the code generator. This option is for codegens that take JSON formatted IR."))

  <|> CodegenArgs <$> strOption (long "cg-opt"
                                 <> metavar "ARG"
                                 <> help "Arguments to pass to code generator")

  <|> EvalExpr <$> strOption (long "eval"
                              <> short 'e'
                              <> metavar "EXPR"
                              <> help "Evaluate an expression without loading the REPL")

  <|> flag' (InterpretScript "Main.main") (long "execute" <> help "Execute as idris")
  <|> InterpretScript <$> strOption      (long "exec" <> metavar "EXPR" <> help "Execute as idris")

  <|> ((Extension . getExt) <$> strOption (long "extension"
                                        <> short 'X'
                                        <> metavar "EXT"
                                        <> help "Turn on language extension (TypeProviders or ErrorReflection)"))

  -- Optimisation Levels
  <|> flag' (OptLevel 3) (long "O3")
  <|> flag' (OptLevel 2) (long "O2")
  <|> flag' (OptLevel 1) (long "O1")
  <|> flag' (OptLevel 0) (long "O0")

  <|> flag' (AddOpt PETransform) (long "partial-eval")
  <|> flag' (RemoveOpt PETransform) (long "no-partial-eval" <> help "Switch off partial evaluation, mainly for debugging purposes")

  <|> OptLevel <$> option auto (short 'O' <> long "level")

  <|> TargetTriple <$> strOption (long "target" <> metavar "TRIPLE" <> help "If supported the codegen will target the named triple.")
  <|> TargetCPU    <$> strOption (long "cpu"    <> metavar "CPU"    <> help "If supported the codegen will target the named CPU e.g. corei7 or cortex-m3")

  -- Colour Options
  <|> flag' (ColourREPL True)  (long "colour"   <> long "color"   <> help "Force coloured output")
  <|> flag' (ColourREPL False) (long "nocolour" <> long "nocolor" <> help "Disable coloured output")

  <|> (UseConsoleWidth <$> option (str >>= parseConsoleWidth) (long "consolewidth" <> metavar "WIDTH" <> help "Select console width: auto, infinite, nat"))

  <|> flag' DumpHighlights (long "highlight" <> help "Emit source code highlighting")

  <|> flag' NoElimDeprecationWarnings      (long "no-elim-deprecation-warnings"   <> help "Disable deprecation warnings for %elim")
  <|> flag' NoOldTacticDeprecationWarnings (long "no-tactic-deprecation-warnings" <> help "Disable deprecation warnings for the old tactic sublanguage")

    where
      getExt :: String -> LanguageExt
      getExt s = fromMaybe (error ("Unknown extension " ++ s)) (maybeRead s)
      maybeRead :: String -> Maybe LanguageExt
      maybeRead = fmap fst . listToMaybe . reads
      portReader :: ReadM REPLPort
      portReader =
        ((ListenPort . fromIntegral) <$> auto) <|>
        (ReadM $ do opt <- ask
                    if map toLower opt == "none"
                      then return $ DontListen
                      else lift $ throwE $ ErrorMsg $
                           "got " <> opt <> " expected port number or \"none\"")

parseVersion :: Parser (a -> a)
parseVersion = infoOption getIdrisVersion (short 'v' <> long "version" <> help "Print version information")

preProcOpts :: [Opt] -> [Opt]
preProcOpts (NoBuiltins : xs) = NoBuiltins : NoPrelude : preProcOpts xs
preProcOpts (Output s : xs)   = Output s : NoREPL : preProcOpts xs
preProcOpts (BCAsm s : xs)    = BCAsm s : NoREPL : preProcOpts xs
preProcOpts (x:xs)            = x : preProcOpts xs
preProcOpts []                = []

parseCodegen :: String -> Codegen
parseCodegen "bytecode" = Bytecode
parseCodegen cg         = Via IBCFormat (map toLower cg)

parseLogCats :: Monad m => String -> m [LogCat]
parseLogCats s =
    case lastMay (readP_to_S doParse s) of
      Just (xs, _) -> return xs
      _            -> fail "Incorrect categories specified"
  where
    doParse :: ReadP [LogCat]
    doParse = do
      cs <- sepBy1 parseLogCat (char ':')
      eof
      return (concat cs)

    parseLogCat :: ReadP [LogCat]
    parseLogCat = (string (strLogCat IParse)    *> return parserCats)
              <|> (string (strLogCat IElab)     *> return elabCats)
              <|> (string (strLogCat ICodeGen)  *> return codegenCats)
              <|> (string (strLogCat ICoverage) *> return [ICoverage])
              <|> (string (strLogCat IIBC)      *> return [IIBC])
              <|> (string (strLogCat IErasure)  *> return [IErasure])
              <|> parseLogCatBad

    parseLogCatBad :: ReadP [LogCat]
    parseLogCatBad = do
      s <- look
      fail $ "Category: " ++ s ++ " is not recognised."

parseConsoleWidth :: Monad m => String -> m ConsoleWidth
parseConsoleWidth "auto"     = return AutomaticWidth
parseConsoleWidth "infinite" = return InfinitelyWide
parseConsoleWidth  s =
  case lastMay (readP_to_S integerReader s) of
     Just (r, _) -> return $ ColsWide r
     _           -> fail $ "Cannot parse: " ++ s

integerReader :: ReadP Int
integerReader = do
    digits <- many1 $ satisfy isDigit
    return $ read digits

{-# LANGUAGE Arrows #-}
module Idris.CmdOptions where

import Idris.AbsSyntaxTree
import Idris.REPL

import IRTS.CodegenCommon

import Options.Applicative
import Options.Applicative.Arrows
import Data.Char
import Data.Maybe

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
                  return $ preProcOpts opts []
               where
                 idrisHeader = PP.hsep [PP.text "Idris version", PP.text ver, PP.text ", (C) The Idris Community 2014"]
                 idrisProgDesc = PP.vsep [PP.empty,
                                          PP.text "Idris is a general purpose pure functional programming language with dependent",
                                          PP.text "types. Dependent types allow types to be predicated on values, meaning that",
                                          PP.text "some aspects of a program's behaviour can be specified precisely in the type.",
                                          PP.text "It is compiled, with eager evaluation. Its features are influenced by Haskell",
                                          PP.text "and ML.",
                                          PP.empty,
                                          PP.vsep $ map (\x -> PP.indent 4 (PP.text x)) [
                                            "+ Full dependent types with dependent pattern matching",
                                            "+ where clauses, with rule, simple case expressions",
                                            "+ pattern matching let and lambda bindings",
                                            "+ Type classes, monad comprehensions",
                                            "+ do notation, idiom brackets",
                                            "+ syntactic conveniences for lists, tuples, dependent pairs",
                                            "+ Totality checking",
                                            "+ Coinductive types",
                                            "+ Indentation significant syntax, extensible syntax",
                                            "+ Tactic based theorem proving (influenced by Coq)",
                                            "+ Cumulative universes",
                                            "+ Simple foreign function interface (to C)",
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
  Just opts -> preProcOpts opts []
  Nothing -> []

parser :: Parser [Opt]
parser = runA $ proc () -> do
  flags <- asA parseFlags -< ()
  files <- asA (many $ argument (fmap Filename str) (metavar "FILES")) -< ()
  A parseVersion >>> A helper -< (flags ++ files)


parseFlags :: Parser [Opt]
parseFlags = many $
  flag' NoBanner (long "nobanner" <> help "Suppress the banner")
  <|> flag' Quiet (short 'q' <> long "quiet" <> help "Quiet verbosity")
  -- IDE Mode Specific Flags
  <|> flag' Idemode (long "ide-mode" <> help "Run the Idris REPL with machine-readable syntax")
  <|> flag' IdemodeSocket (long "ide-mode-socket" <> help "Choose a socket for IDE mode to listen on")
  <|> flag' Idemode (long "ideslave" <> help "Deprecated version of --ide-mode") -- TODO: Remove in v0.9.18
  <|> flag' IdemodeSocket (long "ideslave-socket" <> help "Deprecated version of --ide-mode-socket") -- TODO: Remove in v0.9.18
  <|> (Client <$> strOption (long "client"))
  -- Logging Flags
  <|> (OLogging <$> option auto (long "log" <> metavar "LEVEL" <> help "Debugging log level"))
  -- Turn off Certain libraries.
  <|> flag' NoBasePkgs (long "nobasepkgs" <> help "Do not use the given base package")
  <|> flag' NoPrelude (long "noprelude" <> help "Do not use the given prelude")
  <|> flag' NoBuiltins (long "nobuiltins" <> help "Do not use the builtin functions")
  <|> flag' NoREPL (long "check" <> help "Typecheck only, don't start the REPL")
  <|> (Output <$> strOption (short 'o' <> long "output" <> metavar "FILE" <> help "Specify output file"))
  --   <|> flag' TypeCase (long "typecase")
  <|> flag' Interface (long "interface" <> help "Generate interface files from ExportLists")
  <|> flag' TypeInType (long "typeintype" <> help "Turn off Universe checking")
  <|> flag' DefaultTotal (long "total" <> help "Require functions to be total by default")
  <|> flag' DefaultPartial (long "partial")
  <|> flag' WarnPartial (long "warnpartial" <> help "Warn about undeclared partial functions")
  <|> flag' WarnReach (long "warnreach" <> help "Warn about reachable but inaccessible arguments")
  <|> flag' NoCoverage (long "nocoverage")
  <|> flag' ErrContext (long "errorcontext")
  <|> flag' ShowLibs (long "link" <> help "Display link flags")
  <|> flag' ShowPkgs (long "listlibs" <> help "Display installed libraries")
  <|> flag' ShowLibdir (long "libdir" <> help "Display library directory")
  <|> flag' ShowIncs (long "include" <> help "Display the includes flags")
  <|> flag' Verbose (short 'V' <> long "verbose" <> help "Loud verbosity")
  <|> (IBCSubDir <$> strOption (long "ibcsubdir" <> metavar "FILE" <> help "Write IBC files into sub directory"))
  <|> (ImportDir <$> strOption (short 'i' <> long "idrispath" <> help "Add directory to the list of import paths"))
  <|> flag' WarnOnly (long "warn")
  <|> (Pkg <$> strOption (short 'p' <> long "package" <> help "Add package as a dependency"))
  <|> (Port <$> strOption (long "port" <> metavar "PORT" <> help "REPL TCP port"))
  -- Package commands
  <|> (PkgBuild <$> strOption (long "build" <> metavar "IPKG" <> help "Build package"))
  <|> (PkgInstall <$> strOption (long "install" <> metavar "IPKG" <> help "Install package"))
  <|> (PkgREPL <$> strOption (long "repl" <> metavar "IPKG" <> help "Launch REPL, only for executables"))
  <|> (PkgClean <$> strOption (long "clean" <> metavar "IPKG" <> help "Clean package"))
  <|> (PkgMkDoc <$> strOption (long "mkdoc" <> metavar "IPKG" <> help "Generate IdrisDoc for package"))
  <|> (PkgCheck <$> strOption (long "checkpkg" <> metavar "IPKG" <> help "Check package only"))
  <|> (PkgTest <$> strOption (long "testpkg" <> metavar "IPKG" <> help "Run tests for package"))
  -- Misc options
  <|> (BCAsm <$> strOption (long "bytecode"))
  <|> flag' (OutputTy Raw) (short 'S' <> long "codegenonly" <> help "Do no further compilation of code generator output")
  <|> flag' (OutputTy Object) (short 'c' <> long "compileonly" <> help "Compile to object files rather than an executable")
  <|> flag' (OutputTy MavenProject) (long "mvn" <> help "Create a maven project (for Java codegen)")
  <|> (DumpDefun <$> strOption (long "dumpdefuns"))
  <|> (DumpCases <$> strOption (long "dumpcases"))
  <|> ((\s -> UseCodegen $ parseCodegen s) <$> strOption (long "codegen" <> metavar "TARGET" <> help "Select code generator: C, Javascript, Node and bytecode are bundled with Idris"))
  <|> (CodegenArgs <$> strOption (long "cg-opt" <> metavar "ARG" <> help "Arguments to pass to code generator"))
  <|> (EvalExpr <$> strOption (long "eval" <> short 'e' <> metavar "EXPR" <> help "Evaluate an expression without loading the REPL"))
  <|> flag' (InterpretScript "Main.main") (long "execute" <> help "Execute as idris")
  <|> (InterpretScript <$> strOption (long "exec" <> metavar "EXPR" <> help "Execute as idris"))
  <|> ((\s -> Extension $ getExt s) <$> strOption (long "extension" <> short 'X' <> metavar "EXT" <> help "Turn on language extension (TypeProviders or ErrorReflection)"))
  -- Optimisation Levels
  <|> flag' (OptLevel 3) (long "O3")
  <|> flag' (OptLevel 2) (long "O2")
  <|> flag' (OptLevel 1) (long "O1")
  <|> flag' (OptLevel 0) (long "O0")
  <|> flag' (AddOpt PETransform) (long "partial-eval")
  <|> flag' (RemoveOpt PETransform) (long "no-partial-eval" <> help "Switch off partial evaluation, mainly for debugging purposes")
  <|> (OptLevel <$> option auto (short 'O' <> long "level"))
  <|> (TargetTriple <$> strOption (long "target" <> metavar "TRIPLE" <> help "Select target triple (for llvm codegen)"))
  <|> (TargetCPU <$> strOption (long "cpu" <> metavar "CPU" <> help "Select target CPU e.g. corei7 or cortex-m3 (for LLVM codegen)"))
  -- Colour Options
  <|> flag' (ColourREPL True) (long "colour" <> long "color" <> help "Force coloured output")
  <|> flag' (ColourREPL False) (long "nocolour" <> long "nocolor" <> help "Disable coloured output")

  <|> (UseConsoleWidth <$> option (str >>= parseConsoleWidth) (long "consolewidth" <> metavar "WIDTH" <> help "Select console width: auto, infinite, nat"))
  <|> flag' DumpHighlights (long "highlight" <> help "Emit source code highlighting")
  <|> flag' NoElimDeprecationWarnings (long "no-elim-deprecation-warnings" <> help "Disable deprecation warnings for %elim")
  <|> flag' NoOldTacticDeprecationWarnings (long "no-tactic-deprecation-warnings" <> help "Disable deprecation warnings for the old tactic sublanguage")

  where
    getExt s = case maybeRead s of
      Just ext -> ext
      Nothing -> error ("Unknown extension " ++ s)
    maybeRead = fmap fst . listToMaybe . reads

parseVersion :: Parser (a -> a)
parseVersion = infoOption ver (short 'v' <> long "version" <> help "Print version information")

preProcOpts :: [Opt] -> [Opt] -> [Opt]
preProcOpts [] ys = ys
preProcOpts (NoBuiltins:xs) ys = NoBuiltins : NoPrelude : preProcOpts xs ys
preProcOpts (Output s:xs) ys = Output s : NoREPL : preProcOpts xs ys
preProcOpts (BCAsm s:xs) ys = BCAsm s : NoREPL : preProcOpts xs ys
preProcOpts (x:xs) ys = preProcOpts xs (x:ys)

parseCodegen :: String -> Codegen
parseCodegen "bytecode" = Bytecode
parseCodegen cg = Via (map toLower cg)




parseConsoleWidth :: Monad m => String -> m ConsoleWidth
parseConsoleWidth "auto" = return AutomaticWidth
parseConsoleWidth "infinite" = return InfinitelyWide
parseConsoleWidth  s =
  case lastMay (readP_to_S (integerReader) s) of
     Just (r, _) -> return $ ColsWide r
     _           -> fail $ "Cannot parse: " ++ s



integerReader :: ReadP Int
integerReader = do
    digits <- many1 $ satisfy isDigit
    return $ read digits

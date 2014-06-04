{-# LANGUAGE Arrows #-}
module Idris.CmdOptions where

import Idris.AbsSyntaxTree
import Idris.REPL

import IRTS.CodegenCommon

import Options.Applicative
import Options.Applicative.Arrows
import Data.Maybe

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
                 idrisProgDesc = PP.vsep [PP.text "Idris is a general purpose pure functional programming language with dependent",
                                          PP.text "types. Dependent types allow types to be predicated on values, meaning that",
                                          PP.text "some aspects of a program’s behaviour can be specified precisely in the type.",
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
                                            ],
                                          PP.empty]
                 idrisFooter = PP.vsep [PP.text "It is important to note that Idris is first and foremost a research tool",
                                        PP.text "and project. Thus the tooling provided and resulting programs created",
                                        PP.text "should not necessarily be seen as production ready nor for industrial use.",
                                        PP.empty,
                                        PP.text "More details over Idris can be found online here:",
                                        PP.empty,
                                        PP.indent 4 (PP.text "http://www.idris-lang.org/")]




pureArgParser :: [String] -> [Opt]
pureArgParser args = case execParserMaybe (info parser idm) args of
  Just opts -> preProcOpts opts []
  Nothing -> []

parser :: Parser [Opt]
parser = runA $ proc () -> do
  flags <- asA parseFlags -< ()
  files <- asA (many $ argument ((fmap . fmap) Filename str) (metavar "FILES")) -< ()
  A parseVersion >>> A helper -< (flags ++ files)

parseFlags :: Parser [Opt]
parseFlags = many $
  flag' NoBanner (long "nobanner" <> help "Suppress the banner")
  <|> flag' Quiet (short 'q' <> long "quiet" <> help "Quiet verbosity")
  <|> flag' Ideslave (long "ideslave")
  <|> (Client <$> strOption (long "client"))
  <|> (OLogging <$> option (long "log" <> metavar "LEVEL" <> help "Debugging log level"))
  <|> flag' NoBasePkgs (long "nobasepkgs")
  <|> flag' NoPrelude (long "noprelude")
  <|> flag' NoBuiltins (long "nobuiltins")
  <|> flag' NoREPL (long "check")
  <|> (Output <$> strOption (short 'o' <> long "output" <> metavar "FILE" <> help "Specify output file"))
  <|> flag' TypeCase (long "typecase")
  <|> flag' TypeInType (long "typeintype")
  <|> flag' DefaultTotal (long "total" <> help "Require functions to be total by default")
  <|> flag' DefaultPartial (long "partial")
  <|> flag' WarnPartial (long "warnpartial" <> help "Warn about undeclared partial functions")
  <|> flag' WarnReach (long "warnreach" <> help "Warn about reachable but inaccessible arguments")
  <|> flag' NoCoverage (long "nocoverage")
  <|> flag' ErrContext (long "errorcontext")
  <|> flag' ShowLibs (long "link" <> help "Display link flags")
  <|> flag' ShowLibdir (long "libdir" <> help "Display library directory")
  <|> flag' ShowIncs (long "include" <> help "Display the includes flags")
  <|> flag' Verbose (short 'V' <> long "verbose" <> help "Loud verbosity")
  <|> (IBCSubDir <$> strOption (long "ibcsubdir" <> metavar "FILE" <> help "Write IBC files into sub directory"))
  <|> (ImportDir <$> strOption (short 'i' <> long "idrispath" <> help "Add directory to the list of import paths"))
  <|> flag' WarnOnly (long "warn")
  <|> (Pkg <$> strOption (short 'p' <> long "package"))
  -- Package commands
  <|> (PkgBuild <$> strOption (long "build" <> metavar "IPKG" <> help "Build package"))
  <|> (PkgInstall <$> strOption (long "install" <> metavar "IPKG" <> help "Install package"))
  <|> (PkgREPL <$> strOption (long "repl"))
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
  <|> ((\s -> UseCodegen $ parseCodegen s) <$> strOption (long "codegen" <> metavar "TARGET" <> help "Select code generator: C, Java, bytecode"))
  <|> (EvalExpr <$> strOption (long "eval" <> short 'e' <> metavar "EXPR" <> help "Evaluate an expression without loading the REPL"))
  <|> flag' (InterpretScript "Main.main") (long "execute" <> help "Execute as idris")
  <|> (InterpretScript <$> strOption (long "exec" <> metavar "EXPR" <> help "Execute as idris"))
  <|> ((\s -> Extension $ getExt s) <$> strOption (long "extension" <> short 'X' <> metavar "EXT" <> help "Turn on langage extension (TypeProviders or ErrorReflection)"))
  <|> flag' (OptLevel 3) (long "O3")
  <|> flag' (OptLevel 2) (long "O2")
  <|> flag' (OptLevel 1) (long "O1")
  <|> flag' (OptLevel 0) (long "O0")
  <|> (OptLevel <$> option (short 'O' <> long "level"))
  <|> (TargetTriple <$> strOption (long "target" <> metavar "TRIPLE" <> help "Select target triple (for llvm codegen)"))
  <|> (TargetCPU <$> strOption (long "cpu" <> metavar "CPU" <> help "Select target CPU e.g. corei7 or cortex-m3 (for LLVM codegen)"))
  <|> flag' (ColourREPL True) (long "colour" <> long "color" <> help "Force coloured output")
  <|> flag' (ColourREPL False) (long "nocolour" <> long "nocolor" <> help "Disable coloured output")
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
parseCodegen "C" = ViaC
parseCodegen "Java" = ViaJava
parseCodegen "bytecode" = Bytecode
parseCodegen "javascript" = ViaJavaScript
parseCodegen "node" = ViaNode
parseCodegen "llvm" = ViaLLVM
parseCodegen _ = error "unknown codegen" -- FIXME: partial function

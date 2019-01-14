{-|
Module      : Idris.REPL.Parser
Description : Parser for the REPL commands.
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE FlexibleContexts #-}
module Idris.REPL.Parser (
    parseCmd
  , help
  , allHelp
  , setOptions
  ) where

import Idris.AbsSyntax
import Idris.Colours
import Idris.Core.TT
import Idris.Help
import Idris.Imports
import Idris.Options
import qualified Idris.Parser as IP
import qualified Idris.Parser.Expr as IP
import qualified Idris.Parser.Helpers as IP
import qualified Idris.Parser.Ops as IP

import Idris.REPL.Commands

import Control.Applicative
import Control.Monad.State.Strict
import Data.Char (isSpace, toLower)
import Data.List
import Data.List.Split (splitOn)
import System.Console.ANSI (Color(..))
import System.FilePath ((</>))
import qualified Text.Megaparsec as P

parseCmd :: IState -> String -> String -> Either IP.ParseError (Either String Command)
parseCmd i inputname = IP.runparser pCmd i inputname . trim
    where trim = f . f
              where f = reverse . dropWhile isSpace

type CommandTable = [ ( [String], CmdArg, String
                    , String -> IP.IdrisParser (Either String Command) ) ]

setOptions :: [(String, Opt)]
setOptions = [("errorcontext", ErrContext),
              ("showimplicits", ShowImpl),
              ("originalerrors", ShowOrigErr),
              ("autosolve", AutoSolve),
              ("nobanner", NoBanner),
              ("warnreach", WarnReach),
              ("evaltypes", EvalTypes),
              ("desugarnats", DesugarNats)]

help :: [([String], CmdArg, String)]
help = (["<expr>"], NoArg, "Evaluate an expression") :
  [ (map (':' :) names, args, text) | (names, args, text, _) <- parserCommandsForHelp ]

allHelp :: [([String], CmdArg, String)]
allHelp = [ (map (':' :) names, args, text)
          | (names, args, text, _) <- parserCommandsForHelp ++ parserCommands ]

parserCommandsForHelp :: CommandTable
parserCommandsForHelp =
  [ exprArgCmd ["t", "type"] Check "Check the type of an expression"
  , exprArgCmd ["core"] Core "View the core language representation of a term"
  , nameArgCmd ["miss", "missing"] Missing "Show missing clauses"
  , (["doc"], NameArg, "Show internal documentation", cmd_doc)
  , (["mkdoc"], NamespaceArg, "Generate IdrisDoc for namespace(s) and dependencies"
    , genArg "namespace" (P.many P.anySingle) MakeDoc)
  , (["apropos"], SeqArgs (OptionalArg PkgArgs) NameArg, " Search names, types, and documentation"
    , cmd_apropos)
  , (["s", "search"], SeqArgs (OptionalArg PkgArgs) ExprArg
    , " Search for values by type", cmd_search)
  , nameArgCmd ["wc", "whocalls"] WhoCalls "List the callers of some name"
  , nameArgCmd ["cw", "callswho"] CallsWho "List the callees of some name"
  , namespaceArgCmd ["browse"] Browse "List the contents of some namespace"
  , nameArgCmd ["total"] TotCheck "Check the totality of a name"
  , noArgCmd ["r", "reload"] Reload "Reload current file"
  , noArgCmd ["w", "watch"] Watch "Watch the current file for changes"
  , (["l", "load"], FileArg, "Load a new file"
    , strArg (\f -> Load f Nothing))
  , (["!"], ShellCommandArg, "Run a shell command", strArg RunShellCommand)
  , (["cd"], FileArg, "Change working directory"
    , strArg ChangeDirectory)
  , (["module"], ModuleArg, "Import an extra module", moduleArg ModImport) -- NOTE: dragons
  , noArgCmd ["e", "edit"] Edit "Edit current file using $EDITOR or $VISUAL"
  , noArgCmd ["m", "metavars"] Metavars "Show remaining proof obligations (metavariables or holes)"
  , (["p", "prove"], MetaVarArg, "Prove a metavariable"
    , nameArg (Prove False))
  , (["elab"], MetaVarArg, "Build a metavariable using the elaboration shell"
    , nameArg (Prove True))
  , (["a", "addproof"], NameArg, "Add proof to source file", cmd_addproof)
  , (["rmproof"], NameArg, "Remove proof from proof stack"
    , nameArg RmProof)
  , (["showproof"], NameArg, "Show proof"
    , nameArg ShowProof)
  , noArgCmd ["proofs"] Proofs "Show available proofs"
  , exprArgCmd ["x"] ExecVal "Execute IO actions resulting from an expression using the interpreter"
  , (["c", "compile"], FileArg, "Compile to an executable [codegen] <filename>", cmd_compile)
  , (["exec", "execute"], OptionalArg ExprArg, "Compile to an executable and run", cmd_execute)
  , (["dynamic"], FileArg, "Dynamically load a C library (similar to %dynamic)", cmd_dynamic)
  , (["dynamic"], NoArg, "List dynamically loaded C libraries", cmd_dynamic)
  , noArgCmd ["?", "h", "help"] Help "Display this help text"
  , optArgCmd ["set"] SetOpt $ "Set an option (" ++ optionsList ++ ")"
  , optArgCmd ["unset"] UnsetOpt "Unset an option"
  , (["color", "colour"], ColourArg
    , "Turn REPL colours on or off; set a specific colour"
    , cmd_colour)
  , (["consolewidth"], ConsoleWidthArg, "Set the width of the console", cmd_consolewidth)
  , (["printerdepth"], OptionalArg NumberArg, "Set the maximum pretty-printer depth (no arg for infinite)", cmd_printdepth)
  , noArgCmd ["q", "quit"] Quit "Exit the Idris system"
  , noArgCmd ["version"] ShowVersion "Display the Idris version"
  , noArgCmd ["warranty"] Warranty "Displays warranty information"
  , (["let"], ManyArgs DeclArg
    , "Evaluate a declaration, such as a function definition, instance implementation, or fixity declaration"
    , cmd_let)
  , (["unlet", "undefine"], ManyArgs NameArg
    , "Remove the listed repl definitions, or all repl definitions if no names given"
    , cmd_unlet)
  , nameArgCmd ["printdef"] PrintDef "Show the definition of a function"
  , (["pp", "pprint"], (SeqArgs OptionArg (SeqArgs NumberArg NameArg))
    , "Pretty prints an Idris function in either LaTeX or HTML and for a specified width."
    , cmd_pprint)
  , (["verbosity"], NumberArg, "Set verbosity level", cmd_verb)
  ]
  where optionsList = intercalate ", " $ map fst setOptions


parserCommands :: CommandTable
parserCommands =
  [ noArgCmd ["u", "universes"] Universes "Display universe constraints"
  , noArgCmd ["errorhandlers"] ListErrorHandlers "List registered error handlers"

  , nameArgCmd ["d", "def"] Defn "Display a name's internal definitions"
  , nameArgCmd ["transinfo"] TransformInfo "Show relevant transformation rules for a name"
  , nameArgCmd ["di", "dbginfo"] DebugInfo "Show debugging information for a name"

  , exprArgCmd ["patt"] Pattelab "(Debugging) Elaborate pattern expression"
  , exprArgCmd ["spec"] Spec "?"
  , exprArgCmd ["whnf"] WHNF "(Debugging) Show weak head normal form of an expression"
  , exprArgCmd ["inline"] TestInline "?"
  , proofArgCmd ["cs", "casesplit"] CaseSplitAt
      ":cs <line> <name> splits the pattern variable on the line"
  , proofArgCmd ["apc", "addproofclause"] AddProofClauseFrom
      ":apc <line> <name> adds a pattern-matching proof clause to name on line"
  , proofArgCmd ["ac", "addclause"] AddClauseFrom
      ":ac <line> <name> adds a clause for the definition of the name on the line"
  , proofArgCmd ["am", "addmissing"] AddMissing
      ":am <line> <name> adds all missing pattern matches for the name on the line"
  , proofArgCmd ["mw", "makewith"] MakeWith
      ":mw <line> <name> adds a with clause for the definition of the name on the line"
  , proofArgCmd ["mc", "makecase"] MakeCase
      ":mc <line> <name> adds a case block for the definition of the metavariable on the line"
  , proofArgCmd ["ml", "makelemma"] MakeLemma "?"
  , (["log"], NumberArg, "Set logging level", cmd_log)
  , ( ["logcats"]
    , ManyArgs NameArg
    , "Set logging categories"
    , cmd_cats)
  , (["lto", "loadto"], SeqArgs NumberArg FileArg
    , "Load file up to line number", cmd_loadto)
  , (["ps", "proofsearch"], NoArg
    , ":ps <line> <name> <names> does proof search for name on line, with names as hints"
    , cmd_proofsearch)
  , (["ref", "refine"], NoArg
    , ":ref <line> <name> <name'> attempts to partially solve name on line, with name' as hint, introducing metavariables for arguments that aren't inferrable"
    , cmd_refine)
  , (["debugunify"], SeqArgs ExprArg ExprArg
    , "(Debugging) Try to unify two expressions", const $ do
       l <- IP.simpleExpr defaultSyntax
       r <- IP.simpleExpr defaultSyntax
       P.eof
       return (Right (DebugUnify l r))
    )
  ]

noArgCmd names command doc =
  (names, NoArg, doc, noArgs command)
nameArgCmd names command doc =
  (names, NameArg, doc, fnNameArg command)
namespaceArgCmd names command doc =
  (names, NamespaceArg, doc, namespaceArg command)
exprArgCmd names command doc =
  (names, ExprArg, doc, exprArg command)
optArgCmd names command doc =
  (names, OptionArg, doc, optArg command)
proofArgCmd names command doc =
  (names, NoArg, doc, proofArg command)

pCmd :: IP.IdrisParser (Either String Command)
pCmd = P.choice [ do c <- cmd names; parser c
                | (names, _, _, parser) <- parserCommandsForHelp ++ parserCommands ]
     <|> unrecognized
     <|> nop
     <|> eval
    where nop = do P.eof; return (Right NOP)
          unrecognized = do
              IP.lchar ':'
              cmd <- P.many P.anySingle
              let cmd' = takeWhile (/=' ') cmd
              return (Left $ "Unrecognized command: " ++ cmd')

cmd :: [String] -> IP.IdrisParser String
cmd xs = P.try $ do
    IP.lchar ':'
    docmd sorted_xs

    where docmd [] = fail "Could not parse command"
          docmd (x:xs) = P.try (IP.reserved x >> return x) <|> docmd xs

          sorted_xs = sortBy (\x y -> compare (length y) (length x)) xs


noArgs :: Command -> String -> IP.IdrisParser (Either String Command)
noArgs cmd name = do
    let emptyArgs = do
          P.eof
          return (Right cmd)

    let failure = return (Left $ ":" ++ name ++ " takes no arguments")

    emptyArgs <|> failure

eval :: IP.IdrisParser (Either String Command)
eval = do
  t <- IP.fullExpr defaultSyntax
  return $ Right (Eval t)

exprArg :: (PTerm -> Command) -> String -> IP.IdrisParser (Either String Command)
exprArg cmd name = do
    let noArg = do
          P.eof
          return $ Left ("Usage is :" ++ name ++ " <expression>")

    let justOperator = do
          (op, fc) <- IP.withExtent IP.symbolicOperator
          P.eof
          return $ Right $ cmd (PRef fc [] (sUN op))

    let properArg = do
          t <- IP.fullExpr defaultSyntax
          return $ Right (cmd t)
    P.try noArg <|> P.try justOperator <|> properArg

genArg :: String -> IP.IdrisParser a -> (a -> Command)
           -> String -> IP.IdrisParser (Either String Command)
genArg argName argParser cmd name = do
    let emptyArgs = do P.eof; failure
        oneArg = do arg <- argParser
                    P.eof
                    return (Right (cmd arg))
    P.try emptyArgs <|> oneArg <|> failure
    where
    failure = return $ Left ("Usage is :" ++ name ++ " <" ++ argName ++ ">")

nameArg, fnNameArg :: (Name -> Command) -> String -> IP.IdrisParser (Either String Command)
nameArg = genArg "name" IP.name
fnNameArg = genArg "functionname" IP.fnName

strArg :: (String -> Command) -> String -> IP.IdrisParser (Either String Command)
strArg = genArg "string" (P.many P.anySingle)

moduleArg :: (FilePath -> Command) -> String -> IP.IdrisParser (Either String Command)
moduleArg = genArg "module" (fmap toPath IP.identifier)
  where
    toPath n = foldl1' (</>) $ splitOn "." n

namespaceArg :: ([String] -> Command) -> String -> IP.IdrisParser (Either String Command)
namespaceArg = genArg "namespace" (fmap toNS IP.identifier)
  where
    toNS  = splitOn "."

optArg :: (Opt -> Command) -> String -> IP.IdrisParser (Either String Command)
optArg cmd name = do
    let emptyArgs = do
            P.eof
            return $ Left ("Usage is :" ++ name ++ " <option>")

    let oneArg = do
          o <- pOption
          IP.whiteSpace
          P.eof
          return (Right (cmd o))

    let failure = return $ Left "Unrecognized setting"

    P.try emptyArgs <|> oneArg <|> failure

    where
        pOption :: IP.IdrisParser Opt
        pOption = foldl (<|>) empty $ map (\(a, b) -> do discard (IP.symbol a); return b) setOptions

proofArg :: (Bool -> Int -> Name -> Command) -> String -> IP.IdrisParser (Either String Command)
proofArg cmd name = do
    upd <- P.option False $ do
        IP.lchar '!'
        return True
    l <- IP.natural
    n <- IP.name
    return (Right (cmd upd (fromInteger l) n))

cmd_doc :: String -> IP.IdrisParser (Either String Command)
cmd_doc name = do
    let constant = do
          c <- IP.constant
          P.eof
          return $ Right (DocStr (Right c) FullDocs)

    let pType = do
          IP.reserved "Type"
          P.eof
          return $ Right (DocStr (Left $ sUN "Type") FullDocs)

    let fnName = fnNameArg (\n -> DocStr (Left n) FullDocs) name

    P.try constant <|> pType <|> fnName

cmd_consolewidth :: String -> IP.IdrisParser (Either String Command)
cmd_consolewidth name = do
    w <- pConsoleWidth
    return (Right (SetConsoleWidth w))

    where
        pConsoleWidth :: IP.IdrisParser ConsoleWidth
        pConsoleWidth = do discard (IP.symbol "auto"); return AutomaticWidth
                    <|> do discard (IP.symbol "infinite"); return InfinitelyWide
                    <|> do n <- fromInteger <$> IP.natural
                           return (ColsWide n)

cmd_printdepth :: String -> IP.IdrisParser (Either String Command)
cmd_printdepth _ = do d <- optional (fromInteger <$> IP.natural)
                      return (Right $ SetPrinterDepth d)

cmd_execute :: String -> IP.IdrisParser (Either String Command)
cmd_execute name = do
    tm <- P.option maintm (IP.fullExpr defaultSyntax)
    return (Right (Execute tm))
  where
    maintm = PRef (fileFC "(repl)") [] (sNS (sUN "main") ["Main"])

cmd_dynamic :: String -> IP.IdrisParser (Either String Command)
cmd_dynamic name = do
    let optArg = do l <- P.many P.anySingle
                    if (l /= "")
                        then return $ Right (DynamicLink l)
                        else return $ Right ListDynamic
    let failure = return $ Left $ "Usage is :" ++ name ++ " [<library>]"
    P.try optArg <|> failure

cmd_pprint :: String -> IP.IdrisParser (Either String Command)
cmd_pprint name = do
     fmt <- ppFormat
     IP.whiteSpace
     n <- fromInteger <$> IP.natural
     IP.whiteSpace
     t <- IP.fullExpr defaultSyntax
     return (Right (PPrint fmt n t))

    where
        ppFormat :: IP.IdrisParser OutputFmt
        ppFormat = (discard (IP.symbol "html") >> return HTMLOutput)
               <|> (discard (IP.symbol "latex") >> return LaTeXOutput)

cmd_compile :: String -> IP.IdrisParser (Either String Command)
cmd_compile name = do
    let defaultCodegen = Via IBCFormat "c"

    let codegenOption :: IP.IdrisParser Codegen
        codegenOption = do
            let bytecodeCodegen = discard (IP.symbol "bytecode") *> return Bytecode
                viaCodegen = do x <- IP.identifier
                                return (Via IBCFormat (map toLower x))
            bytecodeCodegen <|> viaCodegen

    let hasOneArg = do
          i <- get
          f <- IP.identifier
          P.eof
          return $ Right (Compile defaultCodegen f)

    let hasTwoArgs = do
          i <- get
          codegen <- codegenOption
          f <- IP.identifier
          P.eof
          return $ Right (Compile codegen f)

    let failure = return $ Left $ "Usage is :" ++ name ++ " [<codegen>] <filename>"
    P.try hasTwoArgs <|> P.try hasOneArg <|> failure

cmd_addproof :: String -> IP.IdrisParser (Either String Command)
cmd_addproof name = do
    n <- P.option Nothing $ do
        x <- IP.name
        return (Just x)
    P.eof
    return (Right (AddProof n))

cmd_log :: String -> IP.IdrisParser (Either String Command)
cmd_log name = do
    i <- fromIntegral <$> IP.natural
    P.eof
    return (Right (LogLvl i))

cmd_verb :: String -> IP.IdrisParser (Either String Command)
cmd_verb name = do
    i <- fromIntegral <$> IP.natural
    P.eof
    return (Right (Verbosity i))

cmd_cats :: String -> IP.IdrisParser (Either String Command)
cmd_cats name = do
    cs <- P.sepBy pLogCats (IP.whiteSpace)
    P.eof
    return $ Right $ LogCategory (concat cs)
  where
    badCat = do
      c <- IP.identifier
      fail $ "Category: " ++ c ++ " is not recognised."

    pLogCats :: IP.IdrisParser [LogCat]
    pLogCats = P.try (parserCats  <$ IP.symbol (strLogCat IParse))
           <|> P.try (elabCats    <$ IP.symbol (strLogCat IElab))
           <|> P.try (codegenCats <$ IP.symbol (strLogCat ICodeGen))
           <|> P.try ([ICoverage] <$ IP.symbol (strLogCat ICoverage))
           <|> P.try ([IIBC]      <$ IP.symbol (strLogCat IIBC))
           <|> P.try ([IErasure]  <$ IP.symbol (strLogCat IErasure))
           <|> badCat

cmd_let :: String -> IP.IdrisParser (Either String Command)
cmd_let name = do
    defn <- concat <$> P.many (IP.decl defaultSyntax)
    return (Right (NewDefn defn))

cmd_unlet :: String -> IP.IdrisParser (Either String Command)
cmd_unlet name = Right . Undefine <$> P.many IP.name

cmd_loadto :: String -> IP.IdrisParser (Either String Command)
cmd_loadto name = do
    toline <- fromInteger <$> IP.natural
    f <- P.many P.anySingle
    return (Right (Load f (Just toline)))

cmd_colour :: String -> IP.IdrisParser (Either String Command)
cmd_colour name = fmap Right pSetColourCmd

    where
        colours :: [(String, Maybe Color)]
        colours = [ ("black", Just Black)
                  , ("red", Just Red)
                  , ("green", Just Green)
                  , ("yellow", Just Yellow)
                  , ("blue", Just Blue)
                  , ("magenta", Just Magenta)
                  , ("cyan", Just Cyan)
                  , ("white", Just White)
                  , ("default", Nothing)
                  ]

        pSetColourCmd :: IP.IdrisParser Command
        pSetColourCmd = (do c <- pColourType
                            let defaultColour = IdrisColour Nothing True False False False
                            opts <- P.sepBy pColourMod (IP.whiteSpace)
                            let colour = foldr ($) defaultColour $ reverse opts
                            return $ SetColour c colour)
                    <|> P.try (IP.symbol "on" >> return ColourOn)
                    <|> P.try (IP.symbol "off" >> return ColourOff)

        pColour :: IP.IdrisParser (Maybe Color)
        pColour = doColour colours
            where doColour [] = fail "Unknown colour"
                  doColour ((s, c):cs) = (P.try (IP.symbol s) >> return c) <|> doColour cs

        pColourMod :: IP.IdrisParser (IdrisColour -> IdrisColour)
        pColourMod = P.try (doVivid <$ IP.symbol "vivid")
                 <|> P.try (doDull <$ IP.symbol "dull")
                 <|> P.try (doUnderline <$ IP.symbol "underline")
                 <|> P.try (doNoUnderline <$ IP.symbol "nounderline")
                 <|> P.try (doBold <$ IP.symbol "bold")
                 <|> P.try (doNoBold <$ IP.symbol "nobold")
                 <|> P.try (doItalic <$ IP.symbol "italic")
                 <|> P.try (doNoItalic <$ IP.symbol "noitalic")
                 <|> P.try (pColour >>= return . doSetColour)
            where doVivid i       = i { vivid = True }
                  doDull i        = i { vivid = False }
                  doUnderline i   = i { underline = True }
                  doNoUnderline i = i { underline = False }
                  doBold i        = i { bold = True }
                  doNoBold i      = i { bold = False }
                  doItalic i      = i { italic = True }
                  doNoItalic i    = i { italic = False }
                  doSetColour c i = i { colour = c }

        -- | Generate the colour type names using the default Show instance.
        colourTypes :: [(String, ColourType)]
        colourTypes = map (\x -> ((map toLower . reverse . drop 6 . reverse . show) x, x)) $
                      enumFromTo minBound maxBound

        pColourType :: IP.IdrisParser ColourType
        pColourType = doColourType colourTypes
            where doColourType [] = fail $ "Unknown colour category. Options: " ++
                                           (concat . intersperse ", " . map fst) colourTypes
                  doColourType ((s,ct):cts) = (P.try (IP.symbol s) >> return ct) <|> doColourType cts

idChar = P.oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['_'])

cmd_apropos :: String -> IP.IdrisParser (Either String Command)
cmd_apropos = packageBasedCmd (some idChar) Apropos

packageBasedCmd :: IP.IdrisParser a -> ([PkgName] -> a -> Command)
                -> String -> IP.IdrisParser (Either String Command)
packageBasedCmd valParser cmd name =
  P.try (do IP.lchar '('
            pkgs <- P.sepBy (pkg <* IP.whiteSpace) (IP.lchar ',')
            IP.lchar ')'
            val <- valParser
            return (Right (cmd pkgs val)))
   <|> do val <- valParser
          return (Right (cmd [] val))
  where
    pkg = either fail pure . pkgName =<< IP.packageName

cmd_search :: String -> IP.IdrisParser (Either String Command)
cmd_search = packageBasedCmd
  (IP.fullExpr (defaultSyntax { implicitAllowed = True })) Search

cmd_proofsearch :: String -> IP.IdrisParser (Either String Command)
cmd_proofsearch name = do
    upd <- P.option False (True <$ IP.lchar '!')
    l <- fromInteger <$> IP.natural; n <- IP.name
    hints <- P.many IP.fnName
    return (Right (DoProofSearch upd True l n hints))

cmd_refine :: String -> IP.IdrisParser (Either String Command)
cmd_refine name = do
   upd <- P.option False (do IP.lchar '!'; return True)
   l <- fromInteger <$> IP.natural; n <- IP.name
   hint <- IP.fnName
   return (Right (DoProofSearch upd False l n [hint]))


module Idris.REPLParser(parseCmd) where

import System.FilePath ((</>))
import System.Console.ANSI (Color(..))

import Idris.Colours
import Idris.AbsSyntax
import Idris.Core.TT
import qualified Idris.Parser as P

import Control.Applicative
import Control.Monad.State.Strict

import Text.Parser.Combinators
import Text.Parser.Char(anyChar)
import Text.Trifecta(Result, parseString)
import Text.Trifecta.Delta

import Debug.Trace
import Data.List
import Data.List.Split(splitOn)
import Data.Char(toLower)
import qualified Data.ByteString.UTF8 as UTF8

parseCmd :: IState -> String -> String -> Result (Either String Command)
parseCmd i inputname = P.runparser pCmd i inputname

pCmd :: P.IdrisParser (Either String Command)
pCmd = do            c <- cmd ["q", "quit"];        noArgs c Quit
              <|> do c <- cmd ["h", "?", "help"];   noArgs c Help
              <|> do c <- cmd ["w", "warranty"];    noArgs c Warranty
              <|> do c <- cmd ["r", "reload"];      noArgs c Reload
              <|> do c <- cmd ["exec", "execute"];  noArgs c Execute
              <|> do c <- cmd ["proofs"];           noArgs c Proofs
              <|> do c <- cmd ["u", "universes"];   noArgs c Universes
              <|> do c <- cmd ["errorhandlers"];    noArgs c ListErrorHandlers
              <|> do c <- cmd ["m", "metavars"];    noArgs c Metavars
              <|> do c <- cmd ["e", "edit"];        noArgs c Edit

              <|> do c <- cmd ["d", "def"];         fnNameArg c Defn
              <|> do c <- cmd ["total"];            fnNameArg c TotCheck
              <|> do c <- cmd ["printdef"];         fnNameArg c PrintDef
              <|> do c <- cmd ["transinfo"];        fnNameArg c TransformInfo
              <|> do c <- cmd ["wc", "whocalls"];   fnNameArg c WhoCalls
              <|> do c <- cmd ["cw", "callswho"];   fnNameArg c CallsWho
              <|> do c <- cmd ["di", "dbginfo"];    fnNameArg c DebugInfo
              <|> do c <- cmd ["miss", "missing"];  fnNameArg c Missing

              <|> do c <- cmd ["t", "type"];        exprArg c Check
              <|> do c <- cmd ["x"];                exprArg c ExecVal
              <|> do c <- cmd ["patt"];             exprArg c Pattelab
              <|> do c <- cmd ["spec"];             exprArg c Spec
              <|> do c <- cmd ["hnf"];              exprArg c HNF
              <|> do c <- cmd ["inline"];           exprArg c TestInline

              <|> do c <- cmd ["rmproof"];          nameArg c RmProof
              <|> do c <- cmd ["showproof"];        nameArg c ShowProof
              <|> do c <- cmd ["p", "prove"];       nameArg c Prove

              <|> do c <- cmd ["set"];              optArg c SetOpt
              <|> do c <- cmd ["unset"];            optArg c UnsetOpt

              <|> do c <- cmd ["l", "load"];        strArg c (\f -> Load f Nothing)
              <|> do c <- cmd ["cd"];               strArg c ChangeDirectory
              <|> do c <- cmd ["apropos"];          strArg c Apropos
              <|> do c <- cmd ["mkdoc"];            strArg c MakeDoc

              <|> do c <- cmd ["cs", "casesplit"];          proofArg c CaseSplitAt
              <|> do c <- cmd ["apc", "addproofclause"];    proofArg c AddProofClauseFrom
              <|> do c <- cmd ["ac", "addclause"];          proofArg c AddClauseFrom
              <|> do c <- cmd ["am", "addmissing"];         proofArg c AddMissing
              <|> do c <- cmd ["mw", "makewith"];           proofArg c MakeWith
              <|> do c <- cmd ["ml", "makelemma"];          proofArg c MakeLemma

              <|> do c <- cmd ["pp", "pprint"];             cmd_pprint c
              <|> do c <- cmd ["doc"];                      cmd_doc c
              <|> do c <- cmd ["dynamic"];                  cmd_dynamic c
              <|> do c <- cmd ["consolewidth"];             cmd_consolewidth c
              <|> do c <- cmd ["module"];                   cmd_module c
              <|> do c <- cmd ["c", "compile"];             cmd_compile c
              <|> do c <- cmd ["a", "addproof"];            cmd_addproof c
              <|> do c <- cmd ["log"];                      cmd_log c
              <|> do c <- cmd ["let"];                      cmd_let c
              <|> do c <- cmd ["unlet","undefine"];         cmd_unlet c
              <|> do c <- cmd ["lto", "loadto"];            cmd_loadto c
              <|> do c <- cmd ["color", "colour"];          cmd_colour c
              <|> do c <- cmd ["s", "search"];              cmd_search c
              <|> do c <- cmd ["ps", "proofsearch"];        cmd_proofsearch c
              <|> do c <- cmd ["ref", "refine"];            cmd_refine c

              <|> unrecognized
              <|> nop
              <|> eval

    where nop = do P.whiteSpace; eof; return (Right NOP)
          eval = exprArg "" Eval
          unrecognized = do 
              P.lchar ':' 
              cmd <- many anyChar
              let cmd' = takeWhile (/=' ') cmd
              return (Left $ "Unrecognized command: " ++ cmd')

cmd :: [String] -> P.IdrisParser String
cmd xs = try $ do 
    P.lchar ':'
    docmd sorted_xs
    
    where docmd [] = fail "Could not parse command"
          docmd (x:xs) = try (P.reserved x >> return x) <|> docmd xs
            
          sorted_xs = sortBy (\x y -> compare (length y) (length x)) xs


noArgs :: String -> Command -> P.IdrisParser (Either String Command)
noArgs name cmd = do
    let emptyArgs = do
        P.whiteSpace
        eof
        return (Right cmd)

    let failure = return (Left $ ":" ++ name ++ " takes no arguments")

    try emptyArgs <|> failure

exprArg :: String -> (PTerm -> Command) -> P.IdrisParser (Either String Command)
exprArg name cmd = do
    P.whiteSpace
    let noArg = do
        eof
        return $ Left ("Usage is :" ++ name ++ " <expression>")

    let properArg = do
        t <- P.fullExpr defaultSyntax
        return $ Right (cmd t)
    try noArg <|> properArg


fnNameArg :: String -> (Name -> Command) -> P.IdrisParser (Either String Command)
fnNameArg name cmd = do
    P.whiteSpace
    let emptyArgs = do eof
                       return $ Left ("Usage is :" ++ name ++ " <functionname>")
        oneArg = do n <- P.fnName
                    eof
                    return (Right (cmd n))
        badArg = return $ Left ("Usage is :" ++ name ++ " <functionname>")
    try emptyArgs <|> try oneArg <|> badArg

nameArg :: String -> (Name -> Command) -> P.IdrisParser (Either String Command)
nameArg name cmd = do
    P.whiteSpace
    let emptyArgs = do eof
                       return $ Left ("Usage is :" ++ name ++ " <functionname>")
        oneArg = do n <- P.name
                    eof
                    return (Right (cmd n))
        badArg = return $ Left ("Usage is :" ++ name ++ " <functionname>")
    try emptyArgs <|> try oneArg <|> badArg

strArg :: String -> (String -> Command) -> P.IdrisParser (Either String Command)
strArg name cmd = do
    n <- many anyChar
    eof
    return (Right (cmd n))

optArg :: String -> (Opt -> Command) -> P.IdrisParser (Either String Command)
optArg name cmd = do
    let emptyArgs = do
            eof
            return $ Left ("Usage is :" ++ name ++ " <option>")

    let oneArg = do
        P.whiteSpace
        o <- pOption
        P.whiteSpace
        eof
        return (Right (cmd o))

    let failure = do
        return $ Left "Unrecognized setting"

    try emptyArgs <|> try oneArg <|> failure

    where
        pOption :: P.IdrisParser Opt
        pOption = do discard (P.symbol "errorcontext"); return ErrContext
              <|> do discard (P.symbol "showimplicits"); return ShowImpl
              <|> do discard (P.symbol "originalerrors"); return ShowOrigErr
              <|> do discard (P.symbol "autosolve"); return AutoSolve
              <|> do discard (P.symbol "nobanner") ; return NoBanner
              <|> do discard (P.symbol "warnreach"); return WarnReach

proofArg :: String -> (Bool -> Int -> Name -> Command) -> P.IdrisParser (Either String Command)
proofArg name cmd = do
    P.whiteSpace
    upd <- option False $ do
        P.lchar '!'
        return True
    l <- P.natural
    n <- P.name;
    return (Right (cmd upd (fromInteger l) n))

cmd_doc :: String -> P.IdrisParser (Either String Command)
cmd_doc name = do
    let constant = do
        c <- P.constant
        eof
        return $ Right (DocStr (Right c))

    let fnName = fnNameArg name (\n -> DocStr (Left n))

    try constant <|> fnName

cmd_consolewidth :: String -> P.IdrisParser (Either String Command)
cmd_consolewidth name = do
    w <- pConsoleWidth
    return (Right (SetConsoleWidth w))

    where
        pConsoleWidth :: P.IdrisParser ConsoleWidth
        pConsoleWidth = do discard (P.symbol "auto"); return AutomaticWidth
                    <|> do discard (P.symbol "infinite"); return InfinitelyWide
                    <|> do n <- fmap fromInteger P.natural; return (ColsWide n)

cmd_dynamic :: String -> P.IdrisParser (Either String Command)
cmd_dynamic name = do
    let emptyArgs = noArgs name ListDynamic

    let oneArg = do l <- many anyChar
                    return $ Right (DynamicLink l)

    let failure = return $ Left $ "Usage is :" ++ name ++ " [<library>]"

    try emptyArgs <|> try oneArg <|> failure

cmd_pprint :: String -> P.IdrisParser (Either String Command)
cmd_pprint name = do
     P.whiteSpace
     fmt <- ppFormat
     P.whiteSpace
     n <- fmap fromInteger P.natural
     P.whiteSpace
     t <- P.fullExpr defaultSyntax
     return (Right (PPrint fmt n t))

    where
        ppFormat :: P.IdrisParser OutputFmt
        ppFormat = (discard (P.symbol "html") >> return HTMLOutput)
               <|> (discard (P.symbol "latex") >> return LaTeXOutput)


cmd_module :: String -> P.IdrisParser (Either String Command)
cmd_module name = do
      f <- P.identifier
      eof;
      return (Right (ModImport (toPath f)))
  where
    toPath n = foldl1' (</>) $ splitOn "." n

cmd_compile :: String -> P.IdrisParser (Either String Command)
cmd_compile name = do
    let defaultCodegen = Via "c"

    let codegenOption :: P.IdrisParser Codegen
        codegenOption = do
            let bytecodeCodegen = discard (P.symbol "bytecode") *> return Bytecode
                viaCodegen = do x <- P.identifier
                                return (Via (map toLower x))
            bytecodeCodegen <|> viaCodegen

    let hasOneArg = do
        i <- get
        f <- P.identifier
        eof
        return $ Right (Compile defaultCodegen f)

    let hasTwoArgs = do
        i <- get
        codegen <- codegenOption
        f <- P.identifier
        eof
        return $ Right (Compile codegen f)

    let failure = return $ Left $ "Usage is :" ++ name ++ " [<codegen>] <filename>"
    try hasTwoArgs <|> try hasOneArg <|> failure

cmd_addproof :: String -> P.IdrisParser (Either String Command)
cmd_addproof name = do
    n <- option Nothing $ do
        x <- P.name;
        return (Just x)
    eof
    return (Right (AddProof n))

cmd_log :: String -> P.IdrisParser (Either String Command)
cmd_log name = do
    i <- P.natural
    eof
    return (Right (LogLvl (fromIntegral i)))

cmd_let :: String -> P.IdrisParser (Either String Command)
cmd_let name = do
    defn <- concat <$> many (P.decl defaultSyntax)
    return (Right (NewDefn defn))

cmd_unlet :: String -> P.IdrisParser (Either String Command)
cmd_unlet name = do
    (Right . Undefine) `fmap` many P.name

cmd_loadto :: String -> P.IdrisParser (Either String Command)
cmd_loadto name = do
    toline <- P.natural
    f <- many anyChar;
    return (Right (Load f (Just (fromInteger toline))))

cmd_colour :: String -> P.IdrisParser (Either String Command)
cmd_colour name = do
    pSetColourCmd >>= return . Right

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

        pSetColourCmd :: P.IdrisParser Command
        pSetColourCmd = (do c <- pColourType
                            let defaultColour = IdrisColour Nothing True False False False
                            opts <- sepBy pColourMod (P.whiteSpace)
                            let colour = foldr ($) defaultColour $ reverse opts
                            return $ SetColour c colour)
                    <|> try (P.symbol "on" >> return ColourOn)
                    <|> try (P.symbol "off" >> return ColourOff)

        pColour :: P.IdrisParser (Maybe Color)
        pColour = doColour colours
            where doColour [] = fail "Unknown colour"
                  doColour ((s, c):cs) = (try (P.symbol s) >> return c) <|> doColour cs

        pColourMod :: P.IdrisParser (IdrisColour -> IdrisColour)
        pColourMod = try (P.symbol "vivid" >> return doVivid)
                 <|> try (P.symbol "dull" >> return doDull)
                 <|> try (P.symbol "underline" >> return doUnderline)
                 <|> try (P.symbol "nounderline" >> return doNoUnderline)
                 <|> try (P.symbol "bold" >> return doBold)
                 <|> try (P.symbol "nobold" >> return doNoBold)
                 <|> try (P.symbol "italic" >> return doItalic)
                 <|> try (P.symbol "noitalic" >> return doNoItalic)
                 <|> try (pColour >>= return . doSetColour)
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

        pColourType :: P.IdrisParser ColourType
        pColourType = doColourType colourTypes
            where doColourType [] = fail $ "Unknown colour category. Options: " ++
                                           (concat . intersperse ", " . map fst) colourTypes
                  doColourType ((s,ct):cts) = (try (P.symbol s) >> return ct) <|> doColourType cts


cmd_search :: String -> P.IdrisParser (Either String Command)
cmd_search name = do
    P.whiteSpace;
    t <- P.typeExpr (defaultSyntax { implicitAllowed = True })
    return (Right (Search t))

cmd_proofsearch :: String -> P.IdrisParser (Either String Command)
cmd_proofsearch name = do
    P.whiteSpace
    upd <- option False (do P.lchar '!'; return True)
    l <- P.natural; n <- P.name;
    hints <- many P.fnName
    return (Right (DoProofSearch upd True (fromInteger l) n hints))

cmd_refine :: String -> P.IdrisParser (Either String Command)
cmd_refine name = do
   P.whiteSpace
   upd <- option False (do P.lchar '!'; return True)
   l <- P.natural; n <- P.name;
   hint <- P.fnName
   return (Right (DoProofSearch upd False (fromInteger l) n [hint]))

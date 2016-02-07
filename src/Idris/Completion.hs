-- | Support for command-line completion at the REPL and in the prover
module Idris.Completion (replCompletion, proverCompletion) where

import Idris.Core.Evaluate (ctxtAlist)
import Idris.Core.TT

import Idris.AbsSyntax (runIO)
import Idris.AbsSyntaxTree
import Idris.Help
import Idris.Imports (installedPackages)
import Idris.Colours
import Idris.Parser.Helpers(opChars)
import qualified Idris.Parser.Expr (constants, tactics)
import Idris.Parser.Expr (TacticArg (..))
import Idris.REPL.Parser (allHelp, setOptions)
import Control.Monad.State.Strict

import Data.List
import Data.Maybe
import Data.Char(toLower)

import System.Console.Haskeline
import System.Console.ANSI (Color)


commands = [ n | (names, _, _) <- allHelp ++ extraHelp, n <- names ]

tacticArgs :: [(String, Maybe TacticArg)]
tacticArgs = [ (name, args) | (names, args, _) <- Idris.Parser.Expr.tactics
                            , name <- names ]
tactics = map fst tacticArgs

-- | Convert a name into a string usable for completion. Filters out names
-- that users probably don't want to see.
nameString :: Name -> Maybe String
nameString (UN nm)
   | not (tnull nm) && (thead nm == '@' || thead nm == '#') = Nothing
nameString (UN n)       = Just (str n)
nameString (NS n _)     = nameString n
nameString _            = Nothing

-- FIXME: Respect module imports
-- Issue #1767 in the issue tracker.
--    https://github.com/idris-lang/Idris-dev/issues/1767
-- | Get the user-visible names from the current interpreter state.
names :: Idris [String]
names = do i <- get
           let ctxt = tt_ctxt i
           return . nub $
             mapMaybe (nameString . fst) (ctxtAlist ctxt) ++
             "Type" : map fst Idris.Parser.Expr.constants

metavars :: Idris [String]
metavars = do i <- get
              return . map (show . nsroot) $ map fst (filter (\(_, (_,_,_,t)) -> not t) (idris_metavars i)) \\ primDefs


modules :: Idris [String]
modules = do i <- get
             return $ map show $ imported i



completeWith :: [String] -> String -> [Completion]
completeWith ns n = if uniqueExists
                    then [simpleCompletion n]
                    else map simpleCompletion prefixMatches
    where prefixMatches = filter (isPrefixOf n) ns
          uniqueExists = [n] == prefixMatches

completeName :: [String] -> String -> Idris [Completion]
completeName extra n = do ns <- names
                          return $ completeWith (extra ++ ns) n

completeExpr :: [String] -> CompletionFunc Idris
completeExpr extra = completeWord Nothing (" \t(){}:" ++ opChars) (completeName extra)

completeMetaVar :: CompletionFunc Idris
completeMetaVar = completeWord Nothing (" \t(){}:" ++ opChars) completeM
    where completeM m = do mvs <- metavars
                           return $ completeWith mvs m

completeOption :: CompletionFunc Idris
completeOption = completeWord Nothing " \t" completeOpt
    where completeOpt = return . completeWith (map fst setOptions)

completeConsoleWidth :: CompletionFunc Idris
completeConsoleWidth = completeWord Nothing " \t" completeW
    where completeW = return . completeWith ["auto", "infinite", "80", "120"]

isWhitespace :: Char -> Bool
isWhitespace = (flip elem) " \t\n"

lookupInHelp :: String -> Maybe CmdArg
lookupInHelp cmd = lookupInHelp' cmd allHelp
    where lookupInHelp' cmd ((cmds, arg, _):xs) | elem cmd cmds = Just arg
                                                | otherwise   = lookupInHelp' cmd xs
          lookupInHelp' cmd [] = Nothing

completeColour :: CompletionFunc Idris
completeColour (prev, next) = case words (reverse prev) of
                                [c] | isCmd c -> do cmpls <- completeColourOpt next
                                                    return (reverse $ c ++ " ", cmpls)
                                [c, o] | o `elem` opts -> let correct = (c ++ " " ++ o) in
                                                          return (reverse correct, [simpleCompletion ""])
                                       | o `elem` colourTypes -> completeColourFormat (prev, next)
                                       | otherwise -> let cmpls = completeWith (opts ++ colourTypes) o in
                                                      let sofar = (c ++ " ") in
                                                      return (reverse sofar, cmpls)
                                cmd@(c:o:_) | isCmd c && o `elem` colourTypes ->
                                        completeColourFormat (prev, next)
                                _ -> noCompletion (prev, next)
    where completeColourOpt :: String -> Idris [Completion]
          completeColourOpt = return . completeWith (opts ++ colourTypes)
          opts = ["on", "off"]
          colourTypes = map (map toLower . reverse . drop 6 . reverse . show) $
                        enumFromTo (minBound::ColourType) maxBound
          isCmd ":colour" = True
          isCmd ":color"  = True
          isCmd _         = False
          colours = map (map toLower . show) $ enumFromTo (minBound::Color) maxBound
          formats = ["vivid", "dull", "underline", "nounderline", "bold", "nobold", "italic", "noitalic"]
          completeColourFormat = let getCmpl = completeWith (colours ++ formats) in
                                 completeWord Nothing " \t" (return . getCmpl)

-- The FIXMEs are Issue #1768 on the issue tracker.
--     https://github.com/idris-lang/Idris-dev/issues/1768
-- | Get the completion function for a particular command
completeCmd :: String -> CompletionFunc Idris
completeCmd cmd (prev, next) = fromMaybe completeCmdName $ fmap completeArg $ lookupInHelp cmd
    where completeArg FileArg = completeFilename (prev, next)
          completeArg NameArg = completeExpr [] (prev, next) -- FIXME only complete one name
          completeArg OptionArg = completeOption (prev, next)
          completeArg ModuleArg = noCompletion (prev, next) -- FIXME do later
          completeArg NamespaceArg = noCompletion (prev, next) -- FIXME do later
          completeArg ExprArg = completeExpr [] (prev, next)
          completeArg MetaVarArg = completeMetaVar (prev, next) -- FIXME only complete one name
          completeArg ColourArg = completeColour (prev, next)
          completeArg NoArg = noCompletion (prev, next)
          completeArg ConsoleWidthArg = completeConsoleWidth (prev, next)
          completeArg DeclArg = completeExpr [] (prev, next)
          completeArg PkgArgs = completePkg (prev, next)
          completeArg (ManyArgs a) = completeArg a
          completeArg (OptionalArg a) = completeArg a
          completeArg (SeqArgs a b) = completeArg a
          completeArg _ = noCompletion (prev, next)
          completeCmdName = return $ ("", completeWith commands cmd)

-- | Complete REPL commands and defined identifiers
replCompletion :: CompletionFunc Idris
replCompletion (prev, next) = case firstWord of
                                ':':cmdName -> completeCmd (':':cmdName) (prev, next)
                                _           -> completeExpr [] (prev, next)
    where firstWord = fst $ break isWhitespace $ dropWhile isWhitespace $ reverse prev


completePkg :: CompletionFunc Idris
completePkg = completeWord Nothing " \t()" completeP
    where completeP p = do pkgs <- runIO installedPackages
                           return $ completeWith pkgs p

-- The TODOs are Issue #1769 on the issue tracker.
--     https://github.com/idris-lang/Idris-dev/issues/1769
completeTactic :: [String] -> String -> CompletionFunc Idris
completeTactic as tac (prev, next) = fromMaybe completeTacName . fmap completeArg $
                                     lookup tac tacticArgs
    where completeTacName = return $ ("", completeWith tactics tac)
          completeArg Nothing              = noCompletion (prev, next)
          completeArg (Just NameTArg)      = noCompletion (prev, next) -- this is for binding new names!
          completeArg (Just ExprTArg)      = completeExpr as (prev, next)
          completeArg (Just StringLitTArg) = noCompletion (prev, next)
          completeArg (Just AltsTArg)      = noCompletion (prev, next) -- TODO

-- | Complete tactics and their arguments
proverCompletion :: [String] -- ^ The names of current local assumptions
                 -> CompletionFunc Idris
proverCompletion assumptions (prev, next) = completeTactic assumptions firstWord (prev, next)
    where firstWord = fst $ break isWhitespace $ dropWhile isWhitespace $ reverse prev

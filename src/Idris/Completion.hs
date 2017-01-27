{-|
Module      : Idris.Completion
Description : Support for command-line completion at the REPL and in the prover.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Completion (replCompletion, proverCompletion) where

import Idris.AbsSyntax (runIO)
import Idris.AbsSyntaxTree
import Idris.Colours
import Idris.Core.Evaluate (ctxtAlist, definitions)
import Idris.Core.TT
import Idris.Help
import Idris.Imports (installedPackages)
import Idris.Parser.Expr (TacticArg(..))
import qualified Idris.Parser.Expr (constants, tactics)
import Idris.Parser.Helpers (opChars)
import Idris.REPL.Parser (allHelp, setOptions)

import Control.Monad.State.Strict
import Data.Char (toLower)
import Data.List
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Text as T
import System.Console.ANSI (Color)
import System.Console.Haskeline

commands = [ n | (names, _, _) <- allHelp ++ extraHelp, n <- names ]

tacticArgs :: [(String, Maybe TacticArg)]
tacticArgs = [ (name, args) | (names, args, _) <- Idris.Parser.Expr.tactics
                            , name <- names ]
tactics = map fst tacticArgs

-- | Get the user-visible names from the current interpreter state.
names :: Idris [String]
names = do i <- get
           let ctxt = tt_ctxt i
           return $
             mapMaybe nameString (allNames $ definitions ctxt) ++
             "Type" : map fst Idris.Parser.Expr.constants
  where
    -- We need both fully qualified names and identifiers that map to them
    allNames :: Ctxt a -> [Name]
    allNames ctxt =
      let mappings = Map.toList ctxt
      in concatMap (\(name, mapping) -> name : Map.keys mapping) mappings
    -- Convert a name into a string usable for completion. Filters out names
    -- that users probably don't want to see.
    nameString :: Name -> Maybe String
    nameString (UN n)       = Just (str n)
    nameString (NS n ns)    =
      let path = intercalate "." . map T.unpack . reverse $ ns
      in fmap ((path ++ ".") ++) $ nameString n
    nameString _            = Nothing

metavars :: Idris [String]
metavars = do i <- get
              return . map (show . nsroot) $ map fst (filter (\(_, (_,_,_,t,_)) -> not t) (idris_metavars i)) \\ primDefs


modules :: Idris [String]
modules = do i <- get
             return $ map show $ imported i

namespaces :: Idris [String]
namespaces = do
  ctxt <- fmap tt_ctxt get
  let names = map fst $ ctxtAlist ctxt
  return $ nub $ catMaybes $ map extractNS names
  where
    extractNS :: Name -> Maybe String
    extractNS (NS n ns) = Just $ intercalate "." . map T.unpack . reverse $ ns
    extractNS _ = Nothing

-- UpTo means if user enters full name then no other completions are shown
-- Full always show other (longer) completions if there are any
data CompletionMode = UpTo | Full deriving Eq

completeWithMode :: CompletionMode -> [String] -> String -> [Completion]
completeWithMode mode ns n =
  if uniqueExists || (fullWord && mode == UpTo)
  then [simpleCompletion n]
  else map simpleCompletion prefixMatches
    where prefixMatches = filter (isPrefixOf n) ns
          uniqueExists = [n] == prefixMatches
          fullWord = n `elem` ns

completeWith = completeWithMode Full

completeName :: CompletionMode -> [String] -> CompletionFunc Idris
completeName mode extra = completeWord Nothing (" \t(){}:" ++ completionWhitespace) completeName
  where
    completeName n = do
      ns <- names
      return $ completeWithMode mode (extra ++ ns) n
    -- The '.' needs not to be taken into consideration because it serves as namespace separator
    completionWhitespace = opChars \\ "."

completeMetaVar :: CompletionFunc Idris
completeMetaVar = completeWord Nothing (" \t(){}:" ++ opChars) completeM
    where completeM m = do mvs <- metavars
                           return $ completeWithMode UpTo mvs m

completeNamespace :: CompletionFunc Idris
completeNamespace = completeWord Nothing " \t" completeN
  where completeN n = do ns <- namespaces
                         return $ completeWithMode UpTo ns n

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
          completeArg ShellCommandArg = completeFilename (prev, next)
          completeArg NameArg = completeName UpTo [] (prev, next)
          completeArg OptionArg = completeOption (prev, next)
          completeArg ModuleArg = noCompletion (prev, next)
          completeArg NamespaceArg = completeNamespace (prev, next)
          completeArg ExprArg = completeName Full [] (prev, next)
          completeArg MetaVarArg = completeMetaVar (prev, next)
          completeArg ColourArg = completeColour (prev, next)
          completeArg NoArg = noCompletion (prev, next)
          completeArg ConsoleWidthArg = completeConsoleWidth (prev, next)
          completeArg DeclArg = completeName Full [] (prev, next)
          completeArg PkgArgs = completePkg (prev, next)
          completeArg (ManyArgs a) = completeArg a
          completeArg (OptionalArg a) = completeArg a
          completeArg (SeqArgs a b) = completeArg a
          completeArg _ = noCompletion (prev, next)
          completeCmdName = return ("", completeWith commands cmd)

-- | Complete REPL commands and defined identifiers
replCompletion :: CompletionFunc Idris
replCompletion (prev, next) = case firstWord of
                                ':':cmdName -> completeCmd (':':cmdName) (prev, next)
                                _           -> completeName UpTo [] (prev, next)
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
    where completeTacName = return ("", completeWith tactics tac)
          completeArg Nothing              = noCompletion (prev, next)
          completeArg (Just NameTArg)      = noCompletion (prev, next) -- this is for binding new names!
          completeArg (Just ExprTArg)      = completeName Full as (prev, next)
          completeArg (Just StringLitTArg) = noCompletion (prev, next)
          completeArg (Just AltsTArg)      = noCompletion (prev, next) -- TODO

-- | Complete tactics and their arguments
proverCompletion :: [String] -- ^ The names of current local assumptions
                 -> CompletionFunc Idris
proverCompletion assumptions (prev, next) = completeTactic assumptions firstWord (prev, next)
    where firstWord = fst $ break isWhitespace $ dropWhile isWhitespace $ reverse prev

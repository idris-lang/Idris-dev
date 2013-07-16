-- | Support for command-line completion at the REPL and in the prover
module Idris.Completion (replCompletion, proverCompletion) where

import Core.Evaluate (ctxtAlist)
import Core.TT
import Core.CoreParser (opChars)

import Idris.AbsSyntaxTree
import Idris.Help

import Control.Monad.State.Strict

import Data.List
import Data.Maybe

import System.Console.Haskeline


fst3 :: (a, b, c) -> a
fst3 (a, b, c) = a

commands = concatMap fst3 help

-- | A specification of the arguments that tactics can take
data TacticArg = NameTArg -- ^ Names: n1, n2, n3, ... n
               | ExprTArg
               | AltsTArg

-- | A list of available tactics and their argument requirements
tacticArgs :: [(String, Maybe TacticArg)]
tacticArgs = [ ("intro", Nothing) -- FIXME syntax for intro (fresh name)
             , ("refine", Just ExprTArg)
             , ("mrefine", Just ExprTArg)
             , ("rewrite", Just ExprTArg)
             , ("let", Nothing) -- FIXME syntax for let
             , ("focus", Just ExprTArg)
             , ("exact", Just ExprTArg)
             , ("applyTactic", Just ExprTArg)
             , ("reflect", Just ExprTArg)
             , ("fill", Just ExprTArg)
             , ("try", Just AltsTArg)
             ] ++ map (\x -> (x, Nothing)) [
              "intros", "compute", "trivial", "solve", "attack",
              "state", "term", "undo", "qed", "abandon", ":q"
             ]
tactics = map fst tacticArgs

-- | Convert a name into a string usable for completion. Filters out names
-- that users probably don't want to see.
nameString :: Name -> Maybe String
nameString (UN ('@':_)) = Nothing
nameString (UN ('#':_)) = Nothing
nameString (UN n)       = Just n
nameString (NS n _)     = nameString n
nameString _            = Nothing

-- FIXME: Respect module imports
-- | Get the user-visible names from the current interpreter state.
names :: Idris [String]
names = do i <- get
           let ctxt = tt_ctxt i
           return . nub $
             mapMaybe (nameString . fst) (ctxtAlist ctxt) ++
             -- Explicitly add primitive types, as these are special-cased in the parser
             ["Int", "Integer", "Float", "Char", "String", "Type",
              "Ptr", "Bits8", "Bits16", "Bits32", "Bits64"]

metavars :: Idris [String]
metavars = do i <- get
              return . map (show . nsroot) $ idris_metavars i \\ primDefs


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
    where completeOpt = return . (completeWith ["errorcontext", "showimplicits"])

isWhitespace :: Char -> Bool
isWhitespace = (flip elem) " \t\n"

lookupInHelp :: String -> Maybe CmdArg
lookupInHelp cmd = lookupInHelp' cmd help
    where lookupInHelp' cmd ((cmds, arg, _):xs) | elem cmd cmds = Just arg
                                                | otherwise   = lookupInHelp' cmd xs
          lookupInHelp' cmd [] = Nothing

-- | Get the completion function for a particular command
completeCmd :: String -> CompletionFunc Idris
completeCmd cmd (prev, next) = fromMaybe completeCmdName $ fmap completeArg $ lookupInHelp cmd
    where completeArg FileArg = completeFilename (prev, next)
          completeArg NameArg = completeExpr [] (prev, next) -- FIXME only complete one name
          completeArg OptionArg = completeOption (prev, next)
          completeArg ModuleArg = noCompletion (prev, next) -- FIXME do later
          completeArg ExprArg = completeExpr [] (prev, next)
          completeArg MetaVarArg = completeMetaVar (prev, next) -- FIXME only complete one name
          completeArg NoArg = noCompletion (prev, next)
          completeCmdName = return $ ("", completeWith commands cmd)

-- | Complete REPL commands and defined identifiers
replCompletion :: CompletionFunc Idris
replCompletion (prev, next) = case firstWord of
                                ':':cmdName -> completeCmd (':':cmdName) (prev, next)
                                _           -> completeExpr [] (prev, next)
    where firstWord = fst $ break isWhitespace $ dropWhile isWhitespace $ reverse prev


completeTactic :: [String] -> String -> CompletionFunc Idris
completeTactic as tac (prev, next) = fromMaybe completeTacName $ fmap completeArg $ lookup tac tacticArgs
    where completeTacName = return $ ("", completeWith tactics tac)
          completeArg Nothing           = noCompletion (prev, next)
          completeArg (Just NameTArg)   = noCompletion (prev, next) -- this is for binding new names!
          completeArg (Just ExprTArg)   = completeExpr as (prev, next)
          completeArg (Just AltsTArg)   = noCompletion (prev, next) -- TODO

-- | Complete tactics and their arguments
proverCompletion :: [String] -- ^ The names of current local assumptions
                 -> CompletionFunc Idris
proverCompletion assumptions (prev, next) = completeTactic assumptions firstWord (prev, next)
    where firstWord = fst $ break isWhitespace $ dropWhile isWhitespace $ reverse prev

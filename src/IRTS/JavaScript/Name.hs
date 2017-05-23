{-|
Module      : IRTS.JavaScript.Name
Description : The JavaScript name mangler.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE OverloadedStrings, PatternGuards #-}

module IRTS.JavaScript.Name
  ( jsName
  , jsNameGenerated
  , Partial(..)
  , jsNamePartial
  , jsTailCallOptimName
  , HiddenClass(..)
  , jsNameHiddenClass
  , dataPartName
  ) where

import Data.Char
import Data.List
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Idris.Core.TT
import IRTS.JavaScript.AST

jsEscape :: String -> String
jsEscape = concatMap jschar
  where
    jschar x
      | isAlpha x || isDigit x = [x]
      | x == '.' = "__"
      | otherwise = "_" ++ show (fromEnum x) ++ "_"

showCGJS :: Name -> String
showCGJS (UN n) = "u$" ++ jsEscape (T.unpack n)
showCGJS (NS n s) = "q_" ++ show (length s) ++ "$" ++ showSep "$" (map (jsEscape . T.unpack) (reverse s))
    ++ "$" ++ showCGJS n
showCGJS (MN _ u) | u == txt "underscore" = "_"
showCGJS (MN i s) = "t$" ++ jsEscape (T.unpack s) ++ "$" ++ show i
showCGJS (SN s) = showCGJS' s
  where
    showCGJS' (WhereN i p c) =
      "where$" ++ showCGJS p ++ "$" ++ showCGJS c ++ "$" ++ show i
    showCGJS' (WithN i n) = "with$" ++ showCGJS n ++ "$" ++ show i
    showCGJS' (ImplementationN cl impl) =
      "impl_" ++ show (length impl) ++ "$" ++ showCGJS cl ++ "$"
        ++ showSep "$" (map (jsEscape . T.unpack) impl)
    showCGJS' (MethodN m) = "meth$" ++ showCGJS m
    showCGJS' (ParentN p c) = "parent$" ++ showCGJS p ++ "$" ++ show c
    showCGJS' (CaseN fc c) = "case$" ++ showCGJS c ++ "$" ++ showFC' fc
    showCGJS' (ElimN sn) = "elim$" ++ showCGJS sn
    showCGJS' (ImplementationCtorN n) = "ictor$" ++ showCGJS n
    showCGJS' (MetaN parent meta) =
      "meta$" ++ showCGJS parent ++ "$" ++ showCGJS meta
    showFC' (FC' NoFC) = ""
    showFC' (FC' (FileFC f)) = "_" ++ cgFN f
    showFC' (FC' (FC f s e))
      | s == e = "_" ++ cgFN f ++ "_" ++ show (fst s) ++ "_" ++ show (snd s)
      | otherwise =
        "_" ++
        cgFN f ++
        "_" ++
        show (fst s) ++
        "_" ++ show (snd s) ++ "_" ++ show (fst e) ++ "_" ++ show (snd e)
    cgFN =
      concatMap
        (\c ->
           if not (isDigit c || isLetter c)
             then "__"
             else [c])
showCGJS (SymRef i) = error "can't do codegen for a symbol reference"

jsName :: Name -> Text
jsName n = T.pack $ showCGJS n

jsNameGenerated :: Int -> Text
jsNameGenerated v = T.pack $ "$cg$" ++ show v

data Partial = Partial Name Int Int deriving (Eq, Ord)

jsNamePartial :: Partial -> Text
jsNamePartial (Partial n i j) = T.concat ["$partial_", T.pack $ show i, "_", T.pack $ show j, "$" , jsName n]

jsTailCallOptimName :: Text -> Text
jsTailCallOptimName x = T.concat ["$tco$", x]


data HiddenClass = HiddenClass Name Int Int deriving (Eq, Ord)

jsNameHiddenClass :: HiddenClass -> Text
jsNameHiddenClass (HiddenClass n id arity) = T.concat ["$HC_", T.pack $ show arity, "_", T.pack $ show id,"$", jsName n]

dataPartName :: Int -> Text
dataPartName i = T.pack $ "$" ++ show i

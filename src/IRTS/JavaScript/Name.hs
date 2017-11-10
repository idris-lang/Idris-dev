{-|
Module      : IRTS.JavaScript.Name
Description : The JavaScript name mangler.

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
import Data.Text (Text)
import qualified Data.Text as T
import Idris.Core.TT

jsEscape :: String -> String
jsEscape = concatMap jschar
  where
    jschar x
      | isAlpha x || isDigit x = [x]
      | x == '.' = "__"
      | otherwise = "_" ++ show (fromEnum x) ++ "_"

jsName :: Name -> Text
jsName (MN i u) = T.concat ["$_", T.pack (show i), "_", T.pack $ jsEscape $ T.unpack u]
jsName n = T.pack $ jsEscape $ showCG n

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

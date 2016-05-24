{-|
Module      : Util.Pretty
Description : Utilities for Pretty Printing.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Util.Pretty (
    module Text.PrettyPrint.Annotated.Leijen
  , Sized(..)
  , nestingSize
  , Pretty(..)
  ) where

--import Text.PrettyPrint.HughesPJ
import Text.PrettyPrint.Annotated.Leijen

-- A rough notion of size for pretty printing various types.
class Sized a where
  size :: a -> Int

instance (Sized a, Sized b) => Sized (a, b) where
  size (left, right) = 1 + size left + size right

instance Sized a => Sized [a] where
  size = sum . map size

nestingSize :: Int
nestingSize = 1

class Pretty a ty where
  pretty :: a -> Doc ty

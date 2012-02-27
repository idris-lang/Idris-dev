module Util.Pretty (
  module Text.PrettyPrint.HughesPJ,
  Sized(..), Pretty(..)
) where

import Text.PrettyPrint.HughesPJ

class Sized a where
  size :: a -> Int

instance (Sized a, Sized b) => Sized (a, b) where
  size (left, right) = 1 + size left + size right

instance Sized a => Sized [a] where
  size = sum . map size

class Pretty a where
  pretty :: a -> Doc

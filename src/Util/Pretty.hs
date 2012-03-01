module Util.Pretty (
  module Text.PrettyPrint.HughesPJ,
  Sized(..), breakingSize, nestingSize,
  Pretty(..)
) where

import Text.PrettyPrint.HughesPJ

-- A rough notion of size for pretty printing various types.
class Sized a where
  size :: a -> Int

instance (Sized a, Sized b) => Sized (a, b) where
  size (left, right) = 1 + size left + size right

instance Sized a => Sized [a] where
  size = sum . map size

-- The maximum size before we break on to another line.
breakingSize :: Int
breakingSize = 15

nestingSize :: Int
nestingSize = 1

class Pretty a where
  pretty :: a -> Doc

instance Pretty () where
  pretty () = text "()"

instance Pretty a => Pretty [a] where
  pretty l = foldr ($$) empty $ map pretty l

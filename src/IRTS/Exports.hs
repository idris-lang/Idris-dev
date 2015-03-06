module IRTS.Exports(findExports) where

import Idris.AbsSyntax
import IRTS.Lang

findExports :: Idris [ExportIFace]
findExports = do exps <- getExports
                 return []


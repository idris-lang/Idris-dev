module Idris.Error where

import Idris.AbsSyntax
import System.IO.Error

report :: IOError -> String
report e
    | isUserError e = ioeGetErrorString e 
    | otherwise     = show e


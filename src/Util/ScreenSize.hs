{-|
Module      : Util.ScreenSize
Description : Utilities for getting screen width.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Util.ScreenSize(getScreenWidth) where

import System.Console.Terminal.Size (size, width)

getScreenWidth :: IO Int
getScreenWidth = maybe 80 width `fmap` size

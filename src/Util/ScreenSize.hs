module Util.ScreenSize(getScreenWidth) where

import System.Console.Terminal.Size (size, width)

getScreenWidth :: IO Int
getScreenWidth = maybe 80 width `fmap` size

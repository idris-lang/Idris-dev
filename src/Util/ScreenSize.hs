module Util.ScreenSize(getScreenWidth) where

import System.Console.Terminal.Size (size, width)
import System.IO (hIsTerminalDevice, stdout)

getScreenWidth :: IO Int
getScreenWidth = do term <- hIsTerminalDevice stdout
                    if term
                      then fmap (maybe 80 width) size
                      else return 80

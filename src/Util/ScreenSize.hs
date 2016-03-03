module Util.ScreenSize(getScreenWidth) where

import System.Console.Terminal.Size (size, width)
import System.IO (hIsTerminalDevice, stdout)

getScreenWidth :: IO Int
getScreenWidth = do term <- hIsTerminalDevice stdout
                    sz <- size 
                    if term
                        then case sz of
                                Just w  -> return $ width w
                                Nothing -> return 80
                        else return 80


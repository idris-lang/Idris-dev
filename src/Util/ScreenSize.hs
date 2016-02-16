{-# LANGUAGE CPP #-}
module Util.ScreenSize(getScreenWidth) where

#ifndef CURSES

getScreenWidth :: IO Int
getScreenWidth = return 80

#else

import UI.HSCurses.Curses
import System.IO (hIsTerminalDevice, stdout)

getScreenWidth :: IO Int
getScreenWidth = do term <- hIsTerminalDevice stdout
                    if term
                       then do
                         initScr
                         refresh
                         size <- scrSize
                         endWin
                         return (snd size)
                       else return 80
#endif

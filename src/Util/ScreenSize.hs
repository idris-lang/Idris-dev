{-# LANGUAGE CPP #-}
module Util.ScreenSize where

import Debug.Trace

#ifndef CURSES

getScreenWidth :: IO Int
getScreenWidth = return 80

#else

import UI.HSCurses.Curses

getScreenWidth :: IO Int
getScreenWidth = do initScr
                    refresh
                    size <- scrSize
                    endWin
                    return (snd size)
#endif

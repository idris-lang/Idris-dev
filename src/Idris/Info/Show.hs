module Idris.Info.Show where

import System.Exit

import Idris.Info

showIdrisFlagsLibs :: IO ()
showIdrisFlagsLibs = do
  libFlags <- getIdrisFlagsLib
  putStrLn $ unwords libFlags

showExitIdrisFlagsLibs :: IO ()
showExitIdrisFlagsLibs = do
  showIdrisFlagsLibs
  exitSuccess

showIdrisLibDir :: IO ()
showIdrisLibDir = do
  ldir <- getIdrisLibDir
  putStrLn ldir

showExitIdrisLibDir :: IO ()
showExitIdrisLibDir = do
  showIdrisLibDir
  exitSuccess

showIdrisFlagsInc :: IO ()
showIdrisFlagsInc = do
  incFlags <- getIdrisFlagsInc
  putStrLn $ unwords incFlags

showExitIdrisFlagsInc :: IO ()
showExitIdrisFlagsInc = do
  showIdrisFlagsInc
  exitSuccess

-- | List idris packages installed
showIdrisInstalledPackages :: IO ()
showIdrisInstalledPackages = do
  ipkgs <- getIdrisInstalledPackages
  mapM_ putStrLn ipkgs

showExitIdrisInstalledPackages :: IO ()
showExitIdrisInstalledPackages = do
  showIdrisInstalledPackages
  exitSuccess

showIdrisLoggingCategories :: IO ()
showIdrisLoggingCategories = do
  cs <- getIdrisLoggingCategories
  mapM_ putStrLn cs

showExitIdrisLoggingCategories :: IO ()
showExitIdrisLoggingCategories = do
  showIdrisLoggingCategories
  exitSuccess

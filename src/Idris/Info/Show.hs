module Idris.Info.Show where

import System.Exit

import Idris.Info


showIdrisFlagsLibs :: IO b
showIdrisFlagsLibs = do
  libFlags <- getIdrisFlagsLib
  putStrLn $ unwords libFlags
  exitSuccess

showIdrisLibDir :: IO b
showIdrisLibDir = do
  ldir <- getIdrisLibDir
  putStrLn ldir
  exitSuccess

showIdrisFlagsInc :: IO b
showIdrisFlagsInc = do
  incFlags <- getIdrisFlagsInc
  putStrLn $ unwords incFlags
  exitSuccess

-- | List idris packages installed
showIdrisInstalledPackages :: IO b
showIdrisInstalledPackages = do
  ipkgs <- getIdrisInstalledPackages
  mapM_ putStrLn ipkgs
  exitSuccess

showIdrisLoggingCategories :: IO b
showIdrisLoggingCategories = do
  cs <- getIdrisLoggingCategories
  mapM_ putStrLn cs
  exitSuccess

module Idris.Info.Show where

import Idris.Info

import System.Exit

showIdrisCRTSDir :: IO ()
showIdrisCRTSDir = do
  ldir <- getIdrisCRTSDir
  putStrLn ldir

showExitIdrisCRTSDir :: IO ()
showExitIdrisCRTSDir = do
  showIdrisCRTSDir
  exitSuccess

showIdrisJSRTSDir :: IO ()
showIdrisJSRTSDir = do
  ldir <- getIdrisJSRTSDir
  putStrLn ldir

showExitIdrisJSRTSDir :: IO ()
showExitIdrisJSRTSDir = do
  showIdrisJSRTSDir
  exitSuccess

showIdrisFlagsLibs :: IO ()
showIdrisFlagsLibs = do
  libFlags <- getIdrisFlagsLib
  putStrLn $ unwords libFlags

showExitIdrisFlagsLibs :: IO ()
showExitIdrisFlagsLibs = do
  showIdrisFlagsLibs
  exitSuccess

showIdrisDataDir :: IO ()
showIdrisDataDir = do
  ldir <- getIdrisDataDir
  putStrLn ldir

showExitIdrisDataDir :: IO ()
showExitIdrisDataDir = do
  showIdrisDataDir
  exitSuccess

showIdrisLibDir :: IO ()
showIdrisLibDir = do
  ldir <- getIdrisLibDir
  putStrLn ldir

showExitIdrisLibDir :: IO ()
showExitIdrisLibDir = do
  showIdrisLibDir
  exitSuccess

showIdrisDocDir :: IO ()
showIdrisDocDir = do
  ldir <- getIdrisDocDir
  putStrLn ldir

showExitIdrisDocDir :: IO ()
showExitIdrisDocDir = do
  showIdrisDocDir
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

showIdrisInfo :: IO ()
showIdrisInfo = do
  putStrLn $ unwords ["Idris", getIdrisVersion]

  ps <- getIdrisInstalledPackages
  putStrLn $ unwords (["Installed Packages:"] ++ ps)

  cs <- getIdrisLoggingCategories
  putStrLn $ unwords (["Logging Categories:"] ++ cs)

  putStrLn "Paths:"
  ldir <- getIdrisLibDir
  udir <- getIdrisUserDataDir
  ddir <- getIdrisDocDir
  idir <- getIdrisDataDir
  crdir <- getIdrisCRTSDir
  jrdir <- getIdrisJSRTSDir
  putStrLn $ unwords ["-", "Data Dir:", idir]
  putStrLn $ unwords ["-", "Library Dir:", ldir]
  putStrLn $ unwords ["-", "C RTS Dir:", crdir]
  putStrLn $ unwords ["-", "JS RTS Dir:", jrdir]
  putStrLn $ unwords ["-", "User Dir:",    udir]
  putStrLn $ unwords ["-", "Documentation Dir:", ddir]

  putStrLn "Flags:"
  lflag <- getIdrisFlagsLib
  iflag <- getIdrisFlagsInc
  eflag <- getIdrisFlagsEnv
  putStrLn $ unwords (["-", "Libraries:", show lflag])
  putStrLn $ unwords (["-", "Includes:",  show iflag])
  putStrLn $ unwords (["-", "Env:",       show eflag])

  cc <- getIdrisCC
  putStrLn $ unwords ["CC:", cc]

  putStrLn "Files:"
  hfile   <- getIdrisHistoryFile
  iscript <- getIdrisInitScript
  putStrLn $ unwords (["-", "History File:",    hfile])
  putStrLn $ unwords (["-", "REPL Init Script", iscript])


showExitIdrisInfo :: IO ()
showExitIdrisInfo = do
  showIdrisInfo
  exitSuccess

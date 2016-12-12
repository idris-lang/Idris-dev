module Idris.Info.Show where

import Idris.Info
import IRTS.System (getInfoStrings)

import System.Exit

showIdrisFlagsLibs :: IO ()
showIdrisFlagsLibs = do
  libFlags <- getIdrisFlagsLib
  putStrLn $ unwords libFlags

showExitIdrisFlagsLibs :: IO ()
showExitIdrisFlagsLibs = do
  showIdrisFlagsLibs
  exitSuccess

showIdrisIdrisdocDir :: IO ()
showIdrisIdrisdocDir = do
  ldir <- getIdrisIdrisdocDir
  putStrLn ldir

showExitIdrisIdrisdocDir :: IO ()
showExitIdrisIdrisdocDir = do
  showIdrisIdrisdocDir
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
  idir <- getIdrisIdrisdocDir
  putStrLn $ unwords ["-", "Library Dir:",       ldir]
  putStrLn $ unwords ["-", "Documentation Dir:", ddir]
  putStrLn $ unwords ["-", "Idrisdoc Dir:",      idir]
  putStrLn $ unwords ["-", "User Dir:",          udir]

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

  putStrLn "Bundled packages:"
  strs <- getInfoStrings
  mapM_ (\(name, val) -> putStrLn $ unwords ["-", name ++ ":", val]) strs


showExitIdrisInfo :: IO ()
showExitIdrisInfo = do
  showIdrisInfo
  exitSuccess

{-|
Module      : Util.DynamicLinker
Description : Platform-specific dynamic linking support. Add new platforms to this file through conditional compilation.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE CPP, ExistentialQuantification, ScopedTypeVariables #-}
module Util.DynamicLinker ( ForeignFun(..)
                          , DynamicLib(..)
                          , tryLoadLib
                          , tryLoadFn
                          ) where

#ifdef IDRIS_FFI
import Foreign.LibFFI
import Foreign.Ptr (FunPtr, Ptr(), castPtrToFunPtr, nullFunPtr, nullPtr)
import System.Directory
#ifndef mingw32_HOST_OS
import Control.Exception (IOException, throwIO, try)
import Data.Array (Array, bounds, inRange, (!))
import Data.Functor ((<$>))
import Data.Maybe (catMaybes)
import System.FilePath.Posix ((</>))
import System.Posix.DynamicLinker
import Text.Regex.TDFA
#else
import qualified Control.Exception as Exception (IOException, catch)
import System.FilePath.Windows ((</>))
import System.Win32.DLL
import System.Win32.Types
type DL = HMODULE
#endif

hostDynamicLibExt :: String
#if defined(linux_HOST_OS) || defined(freebsd_HOST_OS) \
    || defined(dragonfly_HOST_OS) || defined(openbsd_HOST_OS) \
    || defined(netbsd_HOST_OS)
hostDynamicLibExt = "so"
#elif defined(darwin_HOST_OS)
hostDynamicLibExt = "dylib"
#elif defined(mingw32_HOST_OS)
hostDynamicLibExt = "dll"
#else
hostDynamicLibExt = error $ unwords
  [ "Undefined file extension for dynamic libraries"
  , "in Idris' Util.DynamicLinker."
  ]
#endif

data ForeignFun = forall a. Fun { fun_name :: String
                                , fun_handle :: FunPtr a
                                }

data DynamicLib = Lib { lib_name :: String
                      , lib_handle :: DL
                      }

instance Eq DynamicLib where
    (Lib a _) == (Lib b _) = a == b

firstExisting :: [FilePath] -> IO (Maybe FilePath)
firstExisting [] = return Nothing
firstExisting (f:fs) = do exists <- doesFileExist f
                          if exists
                            then return (Just f)
                            else firstExisting fs

libFileName :: [FilePath] -> String -> IO String
libFileName dirs lib = do let names = [lib, lib ++ "." ++ hostDynamicLibExt]
                          cwd <- getCurrentDirectory
                          found <- firstExisting $
                                   map ("."</>) names ++ [d </> f | d <- cwd:dirs, f <- names]
                          return $ maybe (lib ++ "." ++ hostDynamicLibExt) id found

#ifndef mingw32_HOST_OS
-- Load a dynamic library on POSIX systems.
-- In the simple case, we just find the appropriate filename and call dlopen().
-- In the complicated case our "foo.so" isn't actually a library. Some of the
-- .so files on modern Linux systems are linker scripts instead. dlopen()
-- doesn't know anything about those. We need to look inside the script for the
-- actual library path and load that. This is a horrible hack, the correct
-- method would be to actually parse the scripts and execute them. The approach
-- below is what GHC does.
tryLoadLib :: [FilePath] -> String -> IO (Maybe DynamicLib)
tryLoadLib dirs lib = do
  filename <- libFileName dirs lib
  res :: Either IOException DL <- try $
    dlopen filename [RTLD_NOW, RTLD_GLOBAL]
  mbDL <- case res of
    Right handle -> return $ Just handle
#ifdef linux_HOST_OS
    Left ex ->
      -- dlopen failed, run a regex to see if the error message looks like it
      -- could be a linker script.
      case matchAllText invalidLibRegex (show ex) of
        (x:_) -> do
          if inRange (bounds x) 1
            then do
              -- filename above may be a relative path. Get the full path out of
              -- the error message.
              let realPath = fst $ x ! 1
              fileLines <- lines <$> readFile realPath
              -- Go down the linker script line by line looking for .so
              -- filenames and try each one.
              let matches = catMaybes $ map
                    (getLastMatch . matchAllText linkerScriptRegex)
                    fileLines
              mapMFirst (\f -> dlopen f [RTLD_NOW, RTLD_GLOBAL]) matches
            else return Nothing
        [] -> return Nothing
#else
    Left ex -> throwIO ex
#endif
  case mbDL of
    Just handle -> if undl handle == nullPtr
                   then return Nothing
                   else return . Just $ Lib lib handle
    Nothing     -> return Nothing

getLastMatch :: [MatchText String] -> Maybe String
getLastMatch [] = Nothing
getLastMatch (x:_) = case bounds x of
  (low, high) -> if low > high
                 then Nothing
                 else Just $ fst $ x ! high

mapMFirst :: (a -> IO b) -> [a] -> IO (Maybe b)
mapMFirst f []     = return Nothing
mapMFirst f (a:as) = do res <- try (f a)
                        case res of
                          Left (ex :: IOException) -> mapMFirst f as
                          Right res -> return $ Just res

-- Both regexes copyright 2009-2011 Howard B. Golden, CJ van den Berg and Ian
-- Lynagh. From the Glasgow Haskell Compiler. BSD licensed.
invalidLibRegex :: Regex
invalidLibRegex = makeRegex "(([^ \t()])+\\.so([^ \t:()])*):([ \t])*(invalid ELF header|file too short)"

linkerScriptRegex :: Regex
linkerScriptRegex = makeRegex "(GROUP|INPUT) *\\( *([^ )]+)"

tryLoadFn :: String -> DynamicLib -> IO (Maybe ForeignFun)
tryLoadFn fn (Lib _ h) = do cFn <- dlsym h fn
                            if cFn == nullFunPtr
                               then return Nothing
                               else return . Just $ Fun fn cFn
#else
tryLoadLib :: [FilePath] -> String -> IO (Maybe DynamicLib)
tryLoadLib dirs lib = do filename <- libFileName dirs lib
                         handle <- Exception.catch (loadLibrary filename) nullPtrOnException
                         if handle == nullPtr
                             then return Nothing
                             else return . Just $ Lib lib handle
  where nullPtrOnException :: Exception.IOException -> IO DL
        nullPtrOnException e = return nullPtr
        -- `show e` will however give broken error message

tryLoadFn :: String -> DynamicLib -> IO (Maybe ForeignFun)
tryLoadFn fn (Lib _ h) = do cFn <- getProcAddress h fn
                            if cFn == nullPtr
                                then return Nothing
                                else return . Just $ Fun fn (castPtrToFunPtr cFn)
#endif
#else
-- no libffi, just add stubbs.

data DynamicLib = Lib { lib_name :: String
                      , lib_handle :: ()
                      }
    deriving Eq

data ForeignFun = forall a. Fun { fun_name :: String
                                , fun_handle :: ()
                                }

tryLoadLib :: [FilePath] -> String -> IO (Maybe DynamicLib)
tryLoadLib fps lib = do putStrLn $ "WARNING: Cannot load '" ++ lib ++ "' at compile time because Idris was compiled without libffi support."
                        return Nothing

tryLoadFn :: String -> DynamicLib -> IO (Maybe ForeignFun)
tryLoadFn fn lib = do putStrLn $ "WARNING: Cannot load '" ++ fn ++ "' at compile time because Idris was compiled without libffi support."
                      return Nothing
#endif

-- | Platform-specific dynamic linking support. Add new platforms to this file
-- through conditional compilation.
{-# LANGUAGE ExistentialQuantification, CPP #-}
module Util.DynamicLinker where

import Foreign.LibFFI
import Foreign.Ptr (nullPtr, FunPtr, nullFunPtr,castPtrToFunPtr)
import System.Directory
#ifndef WINDOWS
import System.Posix.DynamicLinker
#else
import System.Win32.DLL
import System.Win32.Types
type DL = HMODULE
#endif

hostDynamicLibExt :: String
#ifdef LINUX
hostDynamicLibExt = "so"
#elif MACOSX
hostDynamicLibExt = "dylib"
#elif WINDOWS
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

#ifndef WINDOWS
tryLoadLib :: String -> IO (Maybe DynamicLib)
tryLoadLib lib = do exactName <- doesFileExist lib
                    let filename = if exactName then lib else lib ++ "." ++ hostDynamicLibExt
                    handle <- dlopen filename [RTLD_NOW, RTLD_GLOBAL]
                    if undl handle == nullPtr
                      then return Nothing
                      else return . Just $ Lib lib handle


tryLoadFn :: String -> DynamicLib -> IO (Maybe ForeignFun)
tryLoadFn fn (Lib _ h) = do cFn <- dlsym h fn
                            if cFn == nullFunPtr
                               then return Nothing
                               else return . Just $ Fun fn cFn
#else
tryLoadLib :: String -> IO (Maybe DynamicLib)
tryLoadLib lib = do exactName <- doesFileExist lib
                    let filename = if exactName then lib else lib ++ "." ++ hostDynamicLibExt
                    handle <- loadLibrary filename
                    if handle == nullPtr
                        then return Nothing
                        else return . Just $ Lib lib handle

tryLoadFn :: String -> DynamicLib -> IO (Maybe ForeignFun)
tryLoadFn fn (Lib _ h) = do cFn <- getProcAddress h fn
                            if cFn == nullPtr
                                then return Nothing
                                else return . Just $ Fun fn (castPtrToFunPtr cFn)
#endif

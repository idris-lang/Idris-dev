-- | Platform-specific dynamic linking support. Add new platforms to this file
-- through conditional compilation.
{-# LANGUAGE ExistentialQuantification, CPP #-}
module Util.DynamicLinker where

import Foreign.LibFFI
import Foreign.Ptr (nullPtr, FunPtr, nullFunPtr)
import System.Posix.DynamicLinker

hostDynamicLibExt :: String
#ifdef LINUX
hostDynamicLibExt = "so"
#elif MACOSX
hostDynamicLibExt = "dylib"
#elif WINDOWS
hostDynamicLibExt = "dll"
#endif

data DynamicLib = Lib { lib_name :: String
                      , lib_handle :: DL
                      }

tryLoadLib :: String -> IO (Maybe DynamicLib)
tryLoadLib lib = do handle <- dlopen (lib ++ "." ++ hostDynamicLibExt) [RTLD_NOW]
                    if undl handle == nullPtr
                      then return Nothing
                      else return . Just $ Lib lib handle

data ForeignFun = forall a. Fun { fun_name :: String
                                , fun_handle :: FunPtr a
                                }

tryLoadFn :: String -> DynamicLib -> IO (Maybe ForeignFun)
tryLoadFn fn (Lib _ h) = do cFn <- dlsym h fn
                            if cFn == nullFunPtr
                               then return Nothing
                               else return . Just $ Fun fn cFn

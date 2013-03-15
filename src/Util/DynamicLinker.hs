-- | Platform-specific dynamic linking support. Add new platforms to this file
-- through conditional compilation.

module Util.DynamicLinker where

import Foreign.LibFFI
import Foreign.Ptr (nullPtr)
import System.Posix.DynamicLinker

data DynamicLib = Lib { lib_name :: String
                      , lib_handle :: DL
                      }

tryLoadLib :: String -> IO (Maybe DynamicLib)
tryLoadLib lib = do handle <- dlopen lib [RTLD_NOW]
                    if undl handle == nullPtr
                      then return Nothing
                      else return . Just $ Lib lib handle


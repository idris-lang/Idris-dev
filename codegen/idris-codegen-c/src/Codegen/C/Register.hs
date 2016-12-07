{-# LANGUAGE CPP #-}

module Codegen.C.Register where

import IRTS.System
import IRTS.CodegenC (codegenC)
import System.FilePath (addTrailingPathSeparator, (</>))

getRTSDir = do
  ddir <- getIdrisDataDir
  return $ addTrailingPathSeparator (ddir </> "rts")

register = do
  dir <- getRTSDir
  registerIncFlag ("-I" ++ dir) 80
  registerLibFlag ("-L" ++ dir) 80
  registerLibFlag "-lidris_rts" 81
#ifdef IDRIS_GMP
  registerLibFlag "-lgmp" 99
#endif
  registerLibFlag "-lpthread" 100
  registerInfoString "C RTS Dir" dir
  registerCodeGenerator "C" codegenC

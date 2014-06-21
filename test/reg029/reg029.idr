module Main

import System

-- necessary to find the getenv symbol
%dynamic "libm"

main : IO ()
main = do
  print !(getEnv "IDRIS_REG029_NONEXISTENT_VAR")
  print !(getEnv "IDRIS_REG029_EXISTENT_VAR")

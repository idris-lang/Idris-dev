module Main

import System

%dynamic "libm"

main : IO ()
main = do
  print !(getEnv "IDRIS_REG029_NONEXISTENT_VAR")
  print !(getEnv "IDRIS_REG029_EXISTENT_VAR")

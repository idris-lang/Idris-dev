module Main

import System

-- necessary to find the getenv symbol
%dynamic "libm","msvcrt"

main : IO ()
main = do
  printLn !(getEnv "IDRIS_REG029_NONEXISTENT_VAR")
  printLn !(getEnv "IDRIS_REG029_EXISTENT_VAR")

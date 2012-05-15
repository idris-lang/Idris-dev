module RTS.Assembler where

import RTS.BCParser
import RTS.Bytecode

bcAsm :: FilePath -> IO ()
bcAsm f = do bc <- parseFile f
             print bc

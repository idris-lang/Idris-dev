module Idris.Unlit(unlit) where

import Idris.Core.TT
import Data.Char
import Control.Monad

unlit :: FilePath -> String -> TC String
unlit filePath source = do zipWithM_ (chkAdj filePath) [1..] (pairAdj lineTypes)
                           return finalSource
  where (lineTypes, lineStrings) = unzip $ map parse $ lines source
        finalSource = unlines lineStrings

data LineType = Prog | Blank | Comm

-- By literate haskell standards, source code lines should be extracted
-- by converting the prefix '>' into a space.
parse :: String -> (LineType, String)
parse ('>':xs)            = (Prog,  ' ':xs)
parse xs | all isSpace xs = (Blank, "")
         | otherwise      = (Comm,  "-- " ++ xs)

-- chkAdj checks if the fileTypes of two adjacent lines warrants an error.
chkAdj :: FilePath -> Int -> (LineType, LineType) -> TC ()
chkAdj file lineNumber (Prog, Comm) = adjFail file lineNumber
chkAdj file lineNumber (Comm, Prog) = adjFail file lineNumber
chkAdj _ _ _                        = return ()

-- adjFail is the error returned on an adjacency check failure.
adjFail :: FilePath -> Int -> TC ()
adjFail file lineNumber = tfail $ At range ProgramLineComment
  where range = FC file (lineNumber, 0) (lineNumber, 0)

-- pairAdj converts a list into a list of pairs of adjacent elements.
-- It safely handles single element and empty lists.
pairAdj :: [a] -> [(a,a)]
pairAdj = zip `ap` tail

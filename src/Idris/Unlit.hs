{-|
Module      : Idris.Unlit
Description : Turn literate programs into normal programs.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Unlit(unlit) where

import Idris.Core.TT

import Data.Char

unlit :: FilePath -> String -> TC String
unlit f s = do let s' = map ulLine (lines s)
               check f 1 s'
               return $ unlines (map snd s')

data LineType = Prog | Blank | Comm

ulLine :: String -> (LineType, String)
ulLine ('>':' ':xs)        = (Prog, ' ':' ':xs) -- Replace with spaces, otherwise text position numbers will be bogus.
ulLine ('>':xs)            = (Prog, ' '    :xs) -- The parser can deal with this, because /every/ (code) line is prefixed
                                                -- with a '>'.
ulLine xs | all isSpace xs = (Blank, "")
-- make sure it's not a doc comment
          | otherwise      = (Comm, '-':'-':' ':'>':xs)

check :: FilePath -> Int -> [(LineType, String)] -> TC ()
check f l (a:b:cs) = do chkAdj f l (fst a) (fst b)
                        check f (l+1) (b:cs)
check f l [x] = return ()
check f l [ ] = return ()

-- Issue #1593 on the issue checker.
--
--     https://github.com/idris-lang/Idris-dev/issues/1593
--
chkAdj :: FilePath -> Int -> LineType -> LineType -> TC ()
chkAdj f l Prog Comm = tfail $ At (FC f (l, 0) (l, 0)) ProgramLineComment --TODO: Span correctly
chkAdj f l Comm Prog = tfail $ At (FC f (l, 0) (l, 0)) ProgramLineComment --TODO: Span correctly
chkAdj f l _    _    = return ()

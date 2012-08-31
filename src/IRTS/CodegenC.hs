module IRTS.CodegenC where

import IRTS.Bytecode
import IRTS.Lang
import Core.TT
import Paths_idris

import Data.Char

cname :: Name -> String
cname n = "_idris_" ++ concatMap cchar (show n)
  where cchar x | isAlpha x || isDigit x = [x]
                | otherwise = "_" ++ show (fromEnum x) ++ "_"

indent i = take (i * 4) (repeat ' ')

creg RVal = "RVAL"
creg (L i) = "LOC(" ++ show i ++ ")"
creg (T i) = "TOP(" ++ show i ++ ")"

toDecl :: Name -> String
toDecl f = "void " ++ cname f ++ "(VM*, VAL*);\n" 

toC :: Name -> [BC] -> String
toC f code 
    = -- "/* " ++ show code ++ "*/\n\n" ++ 
      "void " ++ cname f ++ "(VM* vm, VAL* oldbase) {" ++
                 concatMap (bcc 1) code ++ "}\n\n"

bcc :: Int -> BC -> String
bcc i (ASSIGN l r) = indent i ++ creg l ++ " = " ++ creg r ++ ";\n"

bcc i _ = indent i ++ "// not done yet\n"


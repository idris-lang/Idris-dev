{-|
Module      : IRTS.DumpBC
Description : Serialise Idris to its IBC format.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module IRTS.DumpBC where

import Idris.Core.TT
import IRTS.Bytecode
import IRTS.Lang
import IRTS.Simplified

import Data.List

interMap :: [a] -> [b] -> (a -> [b]) -> [b]
interMap xs y f = concat (intersperse y (map f xs))

indent :: Int -> String
indent n = replicate (n*4) ' '

serializeReg :: Reg -> String
serializeReg (L n) = "L" ++ show n
serializeReg (T n) = "T" ++ show n
serializeReg r = show r

serializeCase :: Show a => Int -> (a, [BC]) -> String
serializeCase n (x, bcs) =
  indent n ++ show x ++ ":\n" ++ interMap bcs "\n" (serializeBC (n + 1))

serializeDefault :: Int -> [BC] -> String
serializeDefault n bcs =
  indent n ++ "default:\n" ++ interMap bcs "\n" (serializeBC (n + 1))

serializeBC :: Int -> BC -> String
serializeBC n bc = indent n ++
    case bc of
      ASSIGN a b ->
        "ASSIGN " ++ serializeReg a ++ " " ++ serializeReg b
      ASSIGNCONST a b ->
        "ASSIGNCONST " ++ serializeReg a ++ " " ++ show b
      UPDATE a b ->
        "UPDATE " ++ serializeReg a ++ " " ++ serializeReg b
      MKCON a Nothing b xs ->
        "MKCON " ++ serializeReg a ++ " " ++ show b ++ " [" ++ (interMap xs ", " serializeReg) ++ "]"
      MKCON a (Just r) b xs ->
        "MKCON@" ++ serializeReg r ++ " " ++ serializeReg a ++ " " ++ show b ++ " [" ++ (interMap xs ", " serializeReg) ++ "]"
      CASE safe r cases def ->
        "CASE " ++ serializeReg r ++ ":\n" ++ interMap cases "\n" (serializeCase (n + 1)) ++
        maybe "" (\def' -> "\n" ++ serializeDefault (n + 1) def') def
      PROJECT a b c ->
        "PROJECT " ++ serializeReg a ++ " " ++ show b ++ " " ++ show c
      PROJECTINTO a b c ->
        "PROJECTINTO " ++ serializeReg a ++ " " ++ serializeReg b ++ " " ++ show c
      CONSTCASE r cases def ->
        "CONSTCASE " ++ serializeReg r ++ ":\n" ++ interMap cases "\n" (serializeCase (n + 1)) ++
        maybe "" (\def' -> "\n" ++ serializeDefault (n + 1) def') def
      CALL x -> "CALL " ++ show x
      TAILCALL x -> "TAILCALL " ++ show x
      FOREIGNCALL r ret name args ->
        "FOREIGNCALL " ++ serializeReg r ++ " \"" ++ show name ++ "\" " ++ show ret ++
        " [" ++ interMap args ", " (\(ty, r) -> serializeReg r ++ " : " ++ show ty) ++ "]"
      SLIDE n -> "SLIDE " ++ show n
      REBASE -> "REBASE"
      RESERVE n -> "RESERVE " ++ show n
      ADDTOP n -> "ADDTOP " ++ show n
      TOPBASE n -> "TOPBASE " ++ show n
      BASETOP n -> "BASETOP " ++ show n
      STOREOLD -> "STOREOLD"
      OP a b c ->
        "OP " ++ serializeReg a ++ " " ++ show b ++ " [" ++ interMap c ", " serializeReg ++ "]"
      NULL r -> "NULL " ++ serializeReg r
      ERROR s -> "ERROR \"" ++ s ++ "\"" -- FIXME: s may contain quotes
                                         -- Issue #1596
serialize :: [(Name, [BC])] -> String
serialize decls =
    interMap decls "\n\n" serializeDecl
  where
    serializeDecl :: (Name, [BC]) -> String
    serializeDecl (name, bcs) =
      show name ++ ":\n" ++ interMap bcs "\n" (serializeBC 1)

dumpBC :: [(Name, SDecl)] -> String -> IO ()
dumpBC c output = writeFile output $ serialize $ map toBC c

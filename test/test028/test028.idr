module Main

import Effects
import Effect.File
import Effect.Memory
import Control.IOExcept

MMapIO : Type -> Type -> Type -> Type
MMapIO tf tm r = Eff (IOExcept String) [ Disk ::: FILE_IO tf
                                       , Mem ::: RAW_MEMORY tm ] r

incFirst : Vect Bits8 l -> Vect Bits8 l
incFirst [] = []
incFirst (x :: xs) = (prim__truncInt_B8 . (+ 1) . prim__zextB8_Int $ x) :: xs

testMMap : MMapIO () () String
testMMap = do Disk :- open "testFile" ReadWrite
              l <- Disk :- getLength
              mmap l
              res <- Mem :- peek {i = l} O l
              Mem :- poke {i = l} O (incFirst res)
              Mem :- free
              Disk :- close
              return (pack . toList $ map (prim__intToChar . prim__zextB8_Int) res)

main : IO () 
main = ioe_run (run [Disk := (), Mem := ()] testMMap)
               (\err => print err) (\ok => print ok)

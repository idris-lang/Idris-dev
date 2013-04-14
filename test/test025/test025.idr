module Main

import Effects
import Effect.File
import Effect.Memory
import Control.IOExcept
import Decidable.Order

MemoryIO : Type -> Type -> Type -> Type
MemoryIO td ts r = Eff (IOExcept String) [ Dst ::: RAW_MEMORY td
                                         , Src ::: RAW_MEMORY ts ] r

inpVect : Vect Bits8 5
inpVect = map prim__intToB8 [0, 1, 2, 3, 5]

sub1 : Vect Bits8 n -> Vect Bits8 n
sub1 xs = map (prim__intToB8 . (\ x => x - 1) . prim__B32ToInt . prim__sextB8_32) xs

testMemory : MemoryIO () () (Vect Int 4)
testMemory = do Src :- allocate 5
                Src :- poke {i = O} O inpVect always always
                Dst :- allocate 5
                Dst :- initialize (prim__intToB8 1) 2 always
                move 2 2 3 always always always
                Src :- free
                end <- Dst :- peek 4 1 always
                Dst :- poke 4 (sub1 end) always always
                res <- Dst :- peek 1 4 always
                Dst :- free
                return (map (prim__B32ToInt . prim__sextB8_32) res)
                --return [1, 2, 3, 4]

MMapIO : Type -> Type -> Type -> Type
MMapIO tf tm r = Eff (IOExcept String) [ Disk ::: FILE_IO tf
                                       , Mem ::: RAW_MEMORY tm ] r

outVect : (l : Nat) -> Vect Bits8 l
outVect (S l) = (prim__intToB8 (cast $ S l)) :: outVect l
outVect O = []

lLTEl : Given (Decidable.Order.lte (O + l) l)
lLTEl {l} = ?wtf

testMMap : MMapIO () () (List Char)
testMMap = do Disk :- open "testFile" ReadWrite
              l <- Disk :- getLength
              mmap l
              --Mem :- poke 0 (outVect l) oh
              res <- Mem :- peek {i = l} O l lLTEl
              Mem :- free
              Disk :- close
              --return l
              return (toList $ map (prim__intToChar . prim__B32ToInt . prim__sextB8_32) res)

main : IO ()
main = do ioe_run (run [Dst := (), Src := ()] testMemory)
                  (\err => print err) (\ok => print ok)
          ioe_run (run [Disk := (), Mem := ()] testMMap)
                  (\err => print err) (\ok => print ok)

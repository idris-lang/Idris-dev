module Main 

import Effects
import Effect.Memory
import Control.IOExcept

MemoryIO : Type -> Type -> Type -> Type
MemoryIO td ts r = Eff (IOExcept String) [ Dst ::: RAW_MEMORY td
                                         , Src ::: RAW_MEMORY ts ] r

inpVect : Vect Bits8 5
inpVect = map prim__intToB8 [0, 1, 2, 3, 5]

sub1 : Vect Bits8 n -> Vect Bits8 n
sub1 xs = map (prim__intToB8 . (\ x => x - 1) . prim__B32ToInt . prim__sextB8_32) xs

testMemory : MemoryIO () () (Vect Int 4)
testMemory = do Src :- allocate 5
                Src :- poke 0 inpVect oh
                Dst :- allocate 5
                move 1 1 4 oh oh
                Src :- free
                end <- Dst :- peek 4 1 oh
                Dst :- poke 4 (sub1 end) oh
                res <- Dst :- peek 1 4 oh
                Dst :- free
                return (map (prim__B32ToInt . prim__sextB8_32) res)

main : IO ()
main = do ioe_run (run [Dst := (), Src := ()] testMemory)
                  (\err => print err) (\ok => print ok)



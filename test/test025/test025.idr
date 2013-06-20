module Main

import Effects
import Effect.Memory
import Control.IOExcept

MemoryIO : Type -> Type -> Type -> Type
MemoryIO td ts r = Eff (IOExcept String) [ Dst ::: RAW_MEMORY td
                                         , Src ::: RAW_MEMORY ts ] r

inpVect : Vect Bits8 5
inpVect = map prim__truncInt_B8 [0, 1, 2, 3, 5]

sub1 : Vect Bits8 n -> Vect Bits8 n
sub1 xs = map (prim__truncInt_B8 . (\ x => x - 1) . prim__zextB8_Int) xs

testMemory : MemoryIO () () (Vect Int 4)
testMemory = do Src :- allocate 5
                Src :- poke 0 inpVect oh
                Dst :- allocate 5
                Dst :- initialize (prim__truncInt_B8 1) 2 oh
                move 2 2 3 oh oh
                Src :- free
                end <- Dst :- peek 4 (S O) oh
                Dst :- poke 4 (sub1 end) oh
                res <- Dst :- peek 1 (S(S(S(S O)))) oh
                Dst :- free
                return (map (prim__zextB8_Int) res)

main : IO ()
main = do ioe_run (run [Dst := (), Src := ()] testMemory)
                  (\err => print err) (\ok => print ok)



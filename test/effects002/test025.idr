module Main

import Effects
import Effect.Memory
import Control.IOExcept
import Data.Vect

MemoryIO : Type -> Type -> Type -> Type
MemoryIO td ts r = Eff r [Dst ::: RAW_MEMORY td,
                          Src ::: RAW_MEMORY ts]

inpVect : Vect 5 Bits8
inpVect = map prim__truncInt_B8 [0, 1, 2, 3, 5]

sub1 : Vect n Bits8 -> Vect n Bits8
sub1 xs = map (prim__truncInt_B8 . (\ x => x - 1) . prim__zextB8_Int) xs

testMemory : MemoryIO () () (Vect 4 Int)
testMemory = do Src :- allocate 5
                Src :- poke 0 inpVect Oh
                Dst :- allocate 5
                Dst :- initialize (prim__truncInt_B8 1) 2 Oh
                move 2 2 3 Oh Oh
                Src :- free
                end <- Dst :- peek 4 (S Z) Oh
                Dst :- poke 4 (sub1 end) Oh
                res <- Dst :- peek 1 (S(S(S(S Z)))) Oh
                Dst :- free
                pure (map (prim__zextB8_Int) res)

main : IO ()
main = ioe_run (runInit [Dst := (), Src := ()] testMemory)
               (\err => printLn err) (\ok => printLn ok)



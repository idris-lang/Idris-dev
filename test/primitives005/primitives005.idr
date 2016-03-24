module Main

%include C "memory.h"

-- use calloc to ensure zeroed out memory
malloc : Int -> IO Ptr
malloc size = foreign FFI_C "calloc" (Int -> Int -> IO Ptr) size 1

free : Ptr -> IO ()
free ptr = foreign FFI_C "free" (Ptr -> IO ()) ptr

main : IO ()
main = do
    p <- malloc 1000
    prim_poke16 p 0 0xffff
    prim_poke8 p 8 1
    prim_poke8 p 9 2
    prim_poke8 p 10 3
    prim_poke8 p 11 4
    a <- prim_peek32 p 8
    b <- prim_peek64 p 0
    printLn a
    printLn b
    free p

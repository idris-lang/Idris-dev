module Main

import CFFI
import Data.Vect

%include C "ffi008.h"

size1 : IO Int
size1 = foreign FFI_C "size1" (IO Int)


size2 : IO Int
size2 = foreign FFI_C "size2" (IO Int)

mystruct : IO Ptr
mystruct = foreign FFI_C "&mystruct" (IO Ptr)

print_mystruct : IO ()
print_mystruct = foreign FFI_C "print_mystruct" (IO ())

calc_struct : Ptr -> IO Ptr
calc_struct = foreign FFI_C "calc_struct" (Ptr -> IO Ptr)

test1 : Composite
test1 = STRUCT [I8, I64]

test2 : Composite
test2 = STRUCT [I32, I16]

test3 : Composite
test3 = STRUCT [DOUBLE, DOUBLE, I8, I64]

test4 : Composite
test4 = PACKEDSTRUCT [I8, I8, I8, I64]


main : IO ()
main = do
    printLn $ sizeOf test1 == !size1
    printLn $ sizeOf test2 == !size2
    fms <- pure $ (test2#0) !mystruct
    poke I32 fms 122
    print_mystruct
    printLn $ fields test3
    withAlloc test2 $ \p => do
        f1 <- pure $ (test2 # 0) p
        poke I32 f1 8
        update I32 f1 (* 2)
        print !(peek I32 f1)
    withAlloc PTR $ \p =>
        poke PTR p fms
    res <- withAlloc test1 $ \p => do
        let f1 = (test1 # 0) p
        let f2 = (test1 # 1) p
        poke I8 f1 42
        poke I64 f2 1125899906842624
        calc_struct p
    free res

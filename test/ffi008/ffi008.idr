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

test1 : Composite
test1 = STRUCT [I8, I64]

test2 : Composite
test2 = STRUCT [I32, I16]

test3 : Composite
test3 = STRUCT [DOUBLE, DOUBLE, I8, I64]

test4 : Composite
test4 = PACKEDSTRUCT [I8, I8, I8, I64]

printMore : IO ()
printMore = do
    p <- alloc test3
    f3 <- return $ (test3 # 1) p
    a <- peek DOUBLE f3
    printLn a
    free p
    fms <- return $ (test2#0) !mystruct
    poke I32 fms 122
    print_mystruct
    printLn test4
    printLn !size1
    printLn !size2
    printLn $ fields test3
    printLn $ offsets (STRUCT [I8, I8, I8, I64, test3])
    printLn $ sizeOf (ARRAY 67 I32)
    printLn $ sizeOf test1
    printLn $ sizeOf test2

main : IO ()
main = do
    printLn $ sizeOf test1 == !size1
    printLn $ sizeOf test2 == !size2
    printMore

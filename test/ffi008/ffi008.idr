module Main

import CFFI
import Data.Vect

%include C "ffi008.h"

size1 : IO Int
size1 = foreign FFI_C "size1" (IO Int)


size2 : IO Int
size2 = foreign FFI_C "size2" (IO Int)

test1 : CType
test1 = STRUCT [I8, I64]

test2 : CType
test2 = STRUCT [I32, I16]

test3 : CType
test3 = STRUCT [I8, I8, I8, I64]

test4 : CType
test4 = PACKEDSTRUCT [I8, I8, I8, I64]

printMore : IO ()
printMore = do
    p <- alloc I8
    a <- get p
    free p
    printLn !size1
    printLn !size2
    printLn $ fields test3
    printLn $ offsets (STRUCT [I8, I8, I8, I64, test3])
    printLn $ sizeOf (ARRAY 67 I32)
    printLn $ sizeOf test3

main : IO ()
main = do
    printLn $ sizeOf test1 == !size1
    printLn $ sizeOf test2 == !size2
    printMore

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
    f3 <- return $ p # 1
    a <- peek f3 DOUBLE
    printLn a
    printLn p
    printLn f3
    free p
    ms <- mystruct
    cms <- return $ CPt ms 0 (STRUCT [I32, I16])
    f1 <- return $ cms # 0
    printLn f1
    poke f1 I32 122

    print_mystruct
    printLn test4
    printLn !size1
    printLn !size2
    printLn $ fields test3
    printLn $ offsets (STRUCT [I8, I8, I8, I64, test3])
    printLn $ sizeOfComp (ARRAY 67 I32)
    printLn $ sizeOfComp test3

main : IO ()
main = do
    printLn $ sizeOfComp test1 == !size1
    printLn $ sizeOfComp test2 == !size2
    printMore

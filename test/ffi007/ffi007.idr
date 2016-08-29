module Main

%include c "ffi007.h"

getInt : Int -> Int
getInt _ = 8

test : IO ()
test = foreign FFI_C "test_ffi" (CFnPtr (Int -> Int) -> IO ()) (MkCFnPtr getInt)

strLen : String -> Int
strLen s = cast $ length s

test2 : IO ()
test2 = foreign FFI_C "test_ffi2" (CFnPtr (String -> Int) -> IO ()) (MkCFnPtr strLen)

-- Do IO
printIt : () -> ()
printIt _ = unsafePerformIO $ do
    putStrLn "In an Idris callback"

test3 : IO ()
test3 = foreign FFI_C "test_ffi3" (CFnPtr (() -> ()) -> IO ()) (MkCFnPtr printIt)

test4 : IO Ptr
test4 = foreign FFI_C "%wrapper" (CFnPtr (() -> ()) -> IO Ptr) (MkCFnPtr printIt)

test5 : IO Ptr
test5 = foreign FFI_C "&testvar" (IO Ptr)

test6 : IO Ptr
test6 = foreign FFI_C "test_ffi6" (IO Ptr)

test7 : Ptr -> Int -> IO Int
test7 fnptr i = foreign FFI_C "%dynamic" (Ptr -> Int -> IO Int) fnptr i

adder : Int -> Int -> ()
adder x y = unsafePerformIO $ do
                printLn $ x + y

test8 : IO ()
test8 = foreign FFI_C "test_mulpar" (CFnPtr (Int -> Int -> ()) -> IO ())
                                    (MkCFnPtr adder)

main : IO ()
main = do
            test
            test2
            test3
            ptr <- test4
            tv <- test5
            val <- prim_peek32 tv 0
            printLn val
            fptr <- test6
            i <- test7 fptr 3
            printLn i
            test8
            pure ()

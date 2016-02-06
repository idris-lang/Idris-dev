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
test4 = foreign FFI_C "_idris_get_wrapper" (CFnPtr (() -> ()) -> IO Ptr) (MkCFnPtr printIt)


main : IO ()
main = do
            test
            test2
            test3
            ptr <- test4
            return ()

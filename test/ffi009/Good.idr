module Good

%include c "ffi009.h"

private
get_allocation_size : Ptr -> IO Int
get_allocation_size = foreign FFI_C "get_allocation_size" (Ptr -> IO Int)

-- [ NOTE ]
--
-- As `commen_call` is a partial function and not inline, Idris should complain.

private
%inline
common_call : String -> Int -> IO ManagedPtr
common_call f l = do
  ptr <- foreign FFI_C
                 f
                 (Int -> IO Ptr)
                 l
  len <- get_allocation_size ptr
  pure (prim__registerPtr ptr len)

func_foo : IO ManagedPtr
func_foo = common_call "foo" 4

func_bar : IO ManagedPtr
func_bar = common_call "bar" 8


namespace Main
  main : IO ()
  main = do
    foo <- func_foo
    bar <- func_bar

    printLn "I should be seen."

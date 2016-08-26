impure_op : Bits64 -> IO Bits64
impure_op foo = pure $ foo + 1

impure_int : IO Int
impure_int = pure 41

main : IO ()
main = impure_int >>= impure_op . prim__zextInt_B64 >>= printLn

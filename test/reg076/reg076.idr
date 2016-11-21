data Op = Add | Mul

binop : Op -> Integer -> Integer -> Integer
binop Add = (+)
binop Mul = (*)

doOp : Op -> IO Integer
doOp op = pure (binop op 1 2)

main : IO ()
main = doOp Add >>= print

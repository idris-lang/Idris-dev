%default total

data InfIO : Type -> Type where
     PutStr : String -> InfIO ()
     GetStr : InfIO String
     (>>=) : InfIO a -> (a -> Inf (InfIO b)) -> InfIO b

bad : InfIO a -> InfIO a

echo : InfIO ()
echo = do PutStr "$ "
          x <- GetStr
          PutStr (x ++ "\n")
          case (x == "quit") of
             True => PutStr "Bye!\n"
             False => do PutStr (x ++ "\n")
                         bad echo


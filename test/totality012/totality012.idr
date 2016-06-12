%default total

data InfIO : Type -> Type where
     PutStr : String -> InfIO ()
     GetStr : InfIO String
     (>>=) : InfIO a -> (a -> Inf (InfIO b)) -> InfIO b

echo : InfIO ()
echo = do PutStr "$ "
          x <- GetStr
          PutStr (x ++ "\n")
          case (x == "quit") of
             True => PutStr "Bye!\n"
             False => do PutStr (x ++ "\n")
                         echo
echo1 : InfIO ()
echo1 = do PutStr "$ "
           x <- GetStr
           PutStr (x ++ "\n")
           if (x == "quit") 
              then PutStr "Bye!\n"
              else echo1

echo2 : String -> InfIO ()
echo2 x = case (x == "quit") of
               True => PutStr "Bye!\n"
               False => do PutStr "Foo"
                           echo2 x



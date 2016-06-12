%default total

data InfIO : Type -> Type where
     PutStr : String -> InfIO ()
     GetStr : InfIO String
     (>>=) : InfIO a -> (a -> Inf (InfIO b)) -> InfIO b

echo2 : String -> InfIO ()
echo2 x = if (x == "quit") then PutStr "Bye!\n"
               else echo2 x



%default total

data InfIO : Type -> Type where
     PutStr : String -> InfIO ()
     GetStr : InfIO String
     (>>=) : InfIO a -> (a -> Inf (InfIO b)) -> InfIO b

echo2 : String -> InfIO ()
echo2 x = case (x == "quit") of
               True => PutStr "Bye!\n"
               False => echo2 x



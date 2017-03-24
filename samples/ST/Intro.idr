import Control.ST
import Data.Vect

-- Basic state

-- increment : (x : Var) -> STrans m () [x ::: State Int] 
--                                      (const [x ::: State Int])
increment : (x : Var) -> ST m () [x ::: State Int] 
increment x = do num <- read x
                 write x (num + 1)

-- makeAndIncrement : Int -> STrans m Int [] (const [])
makeAndIncrement : Int -> ST m Int []
makeAndIncrement init = do var <- new init
                           increment var
                           x <- read var
                           delete var
                           pure x

ioMakeAndIncrementBad : STrans IO () [] (const [])
ioMakeAndIncrementBad 
   = do lift $ putStr "Enter a number: "
        init <- lift $ getLine
        var <- new (cast init)
        lift $ putStrLn ("var = " ++ show !(read var))
        increment var
        lift $ putStrLn ("var = " ++ show !(read var))
        delete var

ioMakeAndIncrement : ConsoleIO io => STrans io () [] (const [])
ioMakeAndIncrement 
   = do putStr "Enter a number: "
        init <- getStr
        var <- new (cast init)
        putStrLn ("var = " ++ show !(read var))
        increment var
        putStrLn ("var = " ++ show !(read var))
        delete var

-- Dependent state

-- addElement : (vec : Var) -> (item : a) ->
--              STrans m () [vec ::: State (Vect n a)]
--                   (const [vec ::: State (Vect (S n) a)])
addElement : (vec : Var) -> (item : a) ->
             ST m () [vec ::: State (Vect n a) :-> State (Vect (S n) a)]
addElement vec item = do xs <- read vec
                         write vec (item :: xs)

addElement' : (vec : Var) -> (item : a) ->
              STrans m () [vec ::: State (Vect n a)]
                   (const [vec ::: State (Vect (S n) a)])
addElement' vec item = update vec (item ::)

-- readAndAdd : ConsoleIO io => (vec : Var) ->
--              STrans io Bool [vec ::: State (Vect n Integer)]
--                    (\res => [vec ::: State (if res then Vect (S n) Integer
--                                                    else Vect n Integer)])
readAndAdd : ConsoleIO io => (vec : Var) ->
             ST io Bool 
                   [vec ::: State (Vect n Integer) :->
                            \res => State (if res then Vect (S n) Integer
                                                  else Vect n Integer)]
readAndAdd vec = do putStr "Enter a number: "
                    num <- getStr
                    if all isDigit (unpack num)
                       then returning True (update vec ((cast num) ::))
                       else returning False (pure ())

-- newState : STrans m Var [] (\lbl => [lbl ::: State Int])
newState : ST m Var [add (State Int)]

-- removeState : (lbl : Var) -> STrans m () [lbl ::: State Int] (const [])
removeState : (lbl : Var) -> ST m () [remove lbl (State Int)]


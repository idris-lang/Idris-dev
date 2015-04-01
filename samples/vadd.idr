module Main

import Effects
import Effect.Exception
import Effect.StdIO

parseNumber : String -> { [EXCEPTION String] } Eff Int
parseNumber str
   = if all (\x => isDigit x || x == '-') (unpack str)
        then pure (cast str)
        else raise "Not a number"

vadd : Vect n Int -> Vect n Int -> Vect n Int
vadd [] [] = []
vadd (x :: xs) (y :: ys) = x + y :: vadd xs ys

vadd_check : Vect n Int -> Vect m Int ->
             { [EXCEPTION String] } Eff (Vect m Int)
vadd_check {n} {m} xs ys with (decEq n m)
  vadd_check {n} {m=n} xs ys | (Yes Refl) = pure (vadd xs ys)
  vadd_check {n} {m}   xs ys | (No _)     = raise "Length mismatch"

read_vec : { [STDIO] } Eff (p ** Vect p Int)
read_vec = do putStr "Number (-1 when done): "
              case run {m=Maybe} (parseNumber (trim !getStr)) of
                   Nothing => do putStrLn "Input error"
                                 read_vec
                   Just v => if (v /= -1)
                                then do (_ ** xs) <- read_vec
                                        pure (_ ** v :: xs)
                                else pure (_ ** [])

do_vadd : { [STDIO, EXCEPTION String] } Eff ()
do_vadd = do putStrLn "Vector 1"
             (_ ** xs) <- read_vec
             putStrLn "Vector 2"
             (_ ** ys) <- read_vec
             putStrLn (show !(vadd_check xs ys))

main : IO ()
main = run do_vadd

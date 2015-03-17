import Data.Vect
import Control.Monad.State
import Control.Monad.Identity

VThing : Type
VThing = {n : Nat} -> Vect n Int -> Int

foo : Int -> Vect m Int -> ({n : Nat} -> Vect n Int -> Int) -> Int
foo x xs f = x + f xs

foo' : Int -> Vect m Int -> VThing -> Int
foo' x xs f = x + f xs

bar : Int -> VThing
bar y [] = 0
bar y (x :: xs) = y + x + bar y xs

vsum : Vect n Int -> Int
vsum [] = 0
vsum (x :: xs) = x + vsum xs

testfoo : Vect n Int -> Int
testfoo xs = foo 42 xs (\ xs => vsum xs)

testfoo2 : Vect n Int -> Int
testfoo2 xs = foo' 42 xs vsum

testfoo3 : Vect n Int -> Int
testfoo3 xs = foo 42 xs (bar 10)

AnyST : Type -> Type -> Type
AnyST s a = {m : _} -> Monad m => StateT s m a

-- foost : AnyST Int ()
foost : StateT Int Maybe ()
foost = do x <- get
           put x

wibble : StateT Int Maybe ()
wibble = foost

appShow : Show a => ({b : _} -> Show b => b -> String) -> a -> String
appShow s x = s x

myshow : Show a => a -> String
myshow = show

baz : Int -> String
baz x = appShow myshow x ++ appShow show x

tupleId : ({a : _} -> a -> a) -> (a, b) -> (a, b)
tupleId f (a, b) = (f a, f b)

AppendType : Type
AppendType = {a, n, m : _} -> Vect n a -> Vect m a -> Vect (n + m) a

append : AppendType
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

main : IO ()
main = do putStrLn (baz 42)
          printLn (append [1,2,3] [4,5,6])

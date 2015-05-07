module Main

import System
import Effects
import Effect.StdIO
import Effect.State

data Bar = MkBar ( Vect 1 Nat )
instance Default Bar where
  default = MkBar [0]

record Foo : Type where
  MkFoo : (foos : {[STATE Bar]} Eff Bar ) -> Foo

testBar : Bar
testBar = MkBar [6]

bar_op : Bar -> Bar
bar_op (MkBar [n]) = MkBar [n+n]

testFoo : Foo
testFoo = MkFoo $ pure $ testBar

barNat : Bar -> Nat
barNat (MkBar [ n ]) = n

myBar : { [STATE Bar] } Eff Bar
myBar = do b' <- foos testFoo
           pure b'

getFooBar : Foo -> Bar
getFooBar myFoo = runPure $ do ( pure !(foos myFoo) )

testM : Foo -> {[STATE Bar]} Eff ()
testM myFoo = do
  update bar_op

test_f : { [STATE Bar, STDIO] } Eff ()
test_f = do f' <- foos testFoo
            put $ bar_op f'
            -- update bar_op
            putStrLn $ show $ barNat !get
            -- f' <- foos testFoo
            -- putStrLn ( show (barNat f'))
            -- pure ()

{-mut_test_h : (i : Int) -> BTree a -> IO (Int, BTree (Int, a))
mut_test_h i x = runInit ['B := getFooBar testFoo ]
                    (do x' <- mut_test_h v
                        leaves <- 'Leaves :- get
                        pure (leaves, x'))

mut_test_h : Bar -> {['B ::: STATE Bar]} Eff Bar
mut_test_h v = do
    'V :- update bar_op
    pure v
    -}

hello_world : {[STDIO]} Eff ()
hello_world = putStrLn "Hello, World!"

fpow : (a -> a) -> Nat -> a
fpow n = foldr1 (.) $ replicate n

main : IO ()
main = do run test_f -- (putStrLn $ show $ barNat test_f)
          putStrLn $ show $ barNat $ getFooBar testFoo



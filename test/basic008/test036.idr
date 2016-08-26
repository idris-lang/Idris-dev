module Main

maybechoice : Maybe a -> Maybe a -> Maybe a
maybechoice (Just x) _ = Just x
maybechoice Nothing r = r

unused : a -> a -> a
unused _ s = s

doTest : Maybe Nat
doTest = do
  a <- Nothing
  unused a (pure 3)
 `maybechoice` pure 2

main : IO ()
main = putStrLn . show $ doTest

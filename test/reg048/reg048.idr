module Main
import Data.SortedMap

test : List Int -> IO ()
test xs = do let lst = Data.SortedMap.toList mp
             if length lst /= n 
                then putStrLn $ "wrong length for " ++ show xs
                else do let res = map (\x => lookup x mp) xs
                        let found = mapMaybe id res
                        if length found /= n 
                           then putStrLn $ "some lost in " ++ show xs ++ ": res=" ++ show res 
                                            ++ " toList=" ++ show lst
                           else pure ()

  where  
    mp : SortedMap Int ()
    mp = foldr (\x => \m => insert x () m) empty xs
    n : Nat
    n = length xs

main : IO ()
main = do test [1,2,3]
          test [4,3,2,1]
          test [1,2,3,4]

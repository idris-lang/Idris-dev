allZeroesFromTo : Int -> Int -> String -> Bool
allZeroesFromTo n m str
  = if n < m
    then if strIndex str n == '0'
         then allZeroesFromTo (n+1) m str
         else False
    else True

isNthPowerOfTen : Int -> String -> Bool
isNthPowerOfTen n str
  = let m = cast (length str) in
    if m == n+1
    then strHead str == '1' && allZeroesFromTo 1 m str
    else False

main : IO ()
main = do
  let x = power 10 12468
  let sx = show x
  printLn (isNthPowerOfTen 12468 sx)
  let y = power 10 12470
  let sy = show y
  printLn (isNthPowerOfTen 12470 sy)

module Main

fac : Integer -> Integer
fac 0 = 1
fac n = n*fac(n-1)

binomial : Integer -> Integer -> Integer
binomial n k = divBigInt (fac n) ((fac k)*(fac (n-k)))

sumBinomials : Integer -> Integer
sumBinomials n = foldr (+) 0 (map (\k=>binomial n k) [0..n])

main : IO ()
main = do
	if sumBinomials 1000 - pow 2 1000 == 0 
		then putStrLn "OK"
		else putStrLn "ERROR" 

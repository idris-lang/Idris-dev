module QuasiquoteBasics

import Language.Reflection
import Language.Reflection.Utils

nat : TT
nat = `(Nat)

three : TT
three = `(S (S (S Z)))

twoElems : TT
twoElems = `(with List [(), ()])

copy : TT -> TT
copy q = `((~q,~q))

thing : TT -> TT
thing tm = `(with List [Type, ~tm])

getTyArg : TT -> Maybe TT
getTyArg `(~f ~x) = Just x
getTyArg _ = Nothing




namespace Main
  main : IO ()
  main = do putStrLn . show $ thing (copy nat)
            putStrLn "--------------"
            putStrLn . show $ getTyArg nat
            putStrLn "--------------"
            putStrLn . show $ getTyArg (twoElems)

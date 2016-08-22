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
copy q = `((~q,~q) : (Type, Type))

thing : TT -> TT
thing tm = `(with List [Type, ~tm])

namespace Main
  main : IO ()
  main = do putStrLn . show $ twoElems
            putStrLn "--------------"
            putStrLn . show . thing $ copy nat
            putStrLn "--------------"
            putStrLn . show . copy . copy $ `(Type)

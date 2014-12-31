module GoalQQuote

import Data.Vect
import Language.Reflection
import Language.Reflection.Utils

uCon : TT
uCon = `(() : ())

uTy : TT
uTy = `(() : Type)

isDefault : TT -> Bool
isDefault `(()) = True
isDefault _ = False

pTy : TT -> TT -> TT
pTy a b = `((~a, ~b) : Type)

pair : TT -> TT -> TT
pair a b = `((~a, ~b) : (Nat, Nat))

vect : TT
vect = `([1,2] : Vect 2 Nat)

namespace Main
  main : IO ()
  main = putStrLn $
           if isDefault uCon then "con"
                             else if isDefault uTy then "ty"
                                                   else "neither"

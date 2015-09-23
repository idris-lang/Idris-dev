module ClassName

||| A fancy shower with a constructor
||| @ a the thing to be shown
class MyShow a where
  ||| Build a MyShow
  constructor MkMyShow
  ||| The shower
  ||| @ x will become a string
  myShow : (x : a) -> String

twiceAString : MyShow a => a -> String
twiceAString x = myShow x ++ myShow x

instance MyShow Integer where
  myShow x = show x

badShow : MyShow Integer
badShow = MkMyShow (const "hej")

test1 : twiceAString 2 = "22"
test1 = Refl

test2 : twiceAString @{ClassName.badShow} 2 = "hejhej"
test2 = Refl


||| Superclass fun
class MyMagma a where
  constructor MkMyMagma
  total op : a -> a -> a

||| Semigroup
class MyMagma a => MySemigroup a where
  constructor MkMySemigroup
  total isAssoc : (x, y, z : a) -> op x $ op y z = op (op x y) z

instance [addition] MyMagma Nat where
  op = plus

additionS : MySemigroup Nat
additionS = MkMySemigroup @{addition} plusAssociative

doIt : MySemigroup a => a -> List a -> a
doIt x [] = x
doIt x (y :: xs) = doIt (x `op` y) xs

test : Nat
test = doIt @{additionS} 22 [1,2,3,4]

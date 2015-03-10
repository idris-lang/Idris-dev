||| class
||| @ t a type
class C (t : Type) where
  ||| member of class
  m : t

||| type
data A = B

||| instance of class
instance C A where
  m = B

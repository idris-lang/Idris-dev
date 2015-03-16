||| class
||| @ t a type
class C (t : Type) where
  ||| member of class
  m : t

||| type
data A = B

||| type 2
data D a b = E

||| instance of class
instance C A where
  m = B

||| another instance of class
||| @ a parameter type
instance C (D a b) where
  m = E

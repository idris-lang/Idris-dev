||| interface
||| @ t a type
interface C (t : Type) where
  ||| member of interface
  m : t

||| type
data A = B

||| type 2
data D a b = E

||| implementation of interface
implementation C A where
  m = B

||| another implementation of interface
||| @ a parameter type
implementation C (D a b) where
  m = E

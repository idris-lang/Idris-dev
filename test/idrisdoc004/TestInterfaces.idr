module TestInterfaces

||| This is a test
|||
||| @ a Test arg
public export
interface Test a where
  ||| Test function
  test : a -> Int

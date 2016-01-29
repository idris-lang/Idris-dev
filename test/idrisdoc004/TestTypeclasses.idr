module TestTypeclasses

||| This is a test
|||
||| @ a Test arg
public
interface Test a where
  ||| Test function
  test : a -> Int

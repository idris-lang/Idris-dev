module Main

IntFn : Type -> Type
IntFn = \x => Int -> x
  
instance Show (IntFn a) where
    show x = "<<char fn>>"
  
instance Show (Int -> b) where
    show x = "<<int fn>>"

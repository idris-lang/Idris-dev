module Main

IntFn : Type -> Type
IntFn = \x => Int -> x
  
implementation Show (IntFn a) where
    show x = "<<char fn>>"
  
implementation Show (Int -> b) where
    show x = "<<int fn>>"

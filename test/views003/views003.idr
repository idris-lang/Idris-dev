import System
import Data.List.Views

data Palindrome : List a -> Type where
     PNil : Palindrome []
     POne : Palindrome [x]
     PRec : Palindrome xs -> Palindrome (x :: xs ++ [x])

total
palindrome : DecEq a => (xs : List a) -> Maybe (Palindrome xs)
palindrome xs with (vList xs)
  palindrome [] | VNil = Just PNil
  palindrome [x] | VOne = Just POne
  palindrome (x :: (ys ++ [y])) | (VCons z) with (decEq x y)
    palindrome (y :: (ys ++ [y])) | (VCons urec) | (Yes Refl) 
       = case palindrome ys | urec of
              Nothing => Nothing
              Just x => Just (PRec x)
    palindrome (x :: (ys ++ [y])) | (VCons z) | (No contra) 
       = Nothing

palinBool : DecEq a => List a -> Bool
palinBool xs = case palindrome xs of
                    Nothing => False
                    Just _ => True

main : IO ()
main = do [_, num] <- getArgs
          let list = replicate (cast num) 'a'
          printLn (palinBool list)


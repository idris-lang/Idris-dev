module Parser

import Decidable.Equality

import Solver

ParseErr : Type
ParseErr = String

Parser : Nat -> Type
Parser n = Either ParseErr (b : Board n ** LegalBoard b)

mapM : Monad m => (a -> m b) -> Vect a n -> m (Vect b n)
mapM _ Nil = return Vect.Nil
mapM f (x::xs) = do
  x' <- f x
  xs' <- mapM f xs
  return (Vect.(::) x' xs')

parseToken : String -> Either String (Cell n)
parseToken "." = return Nothing
parseToken "0" = Left "Got cell 0, expected 1-based numbering"
parseToken x = fmap Just (tryParseFin ((cast x) - 1))
  where
    tryParseFin : Int -> Either String (Fin n)
    tryParseFin {n=O} _ = Left ("Given cell " ++ x ++ " out of range")
    tryParseFin {n=S k} 0 = return fO
    tryParseFin {n=S k} x =
      case tryParseFin {n=k} (x-1) of
        Left err => Left err
        Right fin => return (fS fin)

length : Vect a n -> Nat
length {n=n} _ = n

parseCols : {b : Board n} -> Fin n -> LegalBoard b -> Vect String n -> Parser n
parseCols {n=O} _ l _ = Right (_ ** l)
parseCols {n=S k} row l cs = helper last l
  where
    step : {b : Board (S k)} -> LegalBoard b -> Fin (S k) -> Parser (S k)
    step {b=b} l x = do
      tok <- parseToken (index x cs)
      case legalVal b (x, row) tok of
        Yes prf => return (_ ** Step prf l)
        No _ => Left ("Illegal cell " ++ index x cs)

    helper : {b : Board (S k)} -> Fin (S k) -> LegalBoard b -> Parser (S k)
    helper fO l = step l fO
    helper (fS k) l = do
      (_ ** next) <- step l (fS k)
      helper (weaken k) next

parseRows : (b : Board n) -> LegalBoard b -> Vect String n -> Parser n
parseRows {n=O}   _ l _  = Right (_ ** l)
parseRows {n=S k} _ l rs = helper last l
  where
    step : {b : Board (S k)} -> Fin (S k) -> LegalBoard b -> Parser (S k)
    step i l =
      let cs = fromList (words (index i rs)) in
      case decEq (length cs) (S k) of
        No _  => Left "Row length not equal to column height"
        Yes prf => parseCols i l (replace prf cs)

    helper : {b : Board (S k)} -> Fin (S k) -> LegalBoard b -> Parser (S k)
    helper fO l = step fO l
    helper (fS k) l = do
      (_ ** next) <- step (fS k) l
      helper (weaken k) next

parse : String -> Either String (n : Nat ** (b : Board n ** LegalBoard b))
parse str =
  let rows = fromList (lines str) in
  case parseRows {n=length rows} emptyBoard Base rows of
    Left msg => Left msg
    Right board => return (_ ** board)

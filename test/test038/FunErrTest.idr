module FunErrTest

import Language.Reflection
import Language.Reflection.Errors
import Language.Reflection.Utils

%language ErrorReflection

total
cadr :  (xs : List a)
     -> {auto cons1 : isCons xs = True}
     -> {auto cons2 : isCons (tail xs cons1) = True}
     -> a
cadr (x :: (y :: _)) {cons1=refl} {cons2=refl} = y
cadr (x :: [])       {cons1=refl} {cons2=refl} impossible

total
eltsErr : TT -> TT -> Maybe (List ErrorReportPart)
eltsErr (P (DCon _ _) (NS (UN "False") _) _) (P (DCon _ _) (NS (UN "True") _) _) =
  Just [  NamePart (NS (UN "cadr") ["FunErrTest"])
       , TextPart "requires that its argument contain at least two elements."
       ]
eltsErr (P (DCon _ _) (NS (UN "True") _) _) (App (App isCons ty) xs) =
  Just [ NamePart (NS (UN "cadr") ["FunErrTest"])
       , TextPart "requires that its argument contain at least two elements."
       , TextPart "This fails because: "
       , SubReport [ TextPart "There is no proof that"
                   , TermPart xs
                   , TextPart "is non-empty."
                   ]
       ]
eltsErr _ _ = Nothing

total
has2elts : Err -> Maybe (List ErrorReportPart)
has2elts (CantUnify _ tm1 tm2 e _ _) = eltsErr tm1 tm2 <|> has2elts e
has2elts e = Just [TextPart (show e)]

%error_handlers cadr cons1 has2elts
%error_handlers cadr cons2 has2elts

problem1 : List a -> a
problem1 xs = cadr xs

problem2 : Int
problem2 = cadr [1]

problem3 : Int
problem3 = cadr []
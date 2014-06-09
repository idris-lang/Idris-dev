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
cadr []              {cons1=refl} {cons2=refl} impossible

extractList : TT -> Maybe TT
extractList (App (App reflCon (App isCons lst)) _) = Just lst
extractList _ = Nothing

total
has2elts : Err -> Maybe (List ErrorReportPart)
has2elts (CantSolveGoal tm _) = do lst <- extractList tm
                                   return [ TextPart "Could not prove that"
                                          , TermPart lst
                                          , TextPart "has at least two elements."
                                          ]
has2elts e = Just [TextPart (show e)]

%error_handlers cadr cons1 has2elts
%error_handlers cadr cons2 has2elts

badCadr1 : Int
badCadr1 = cadr []

badCadr2 : Int
badCadr2 = cadr [1]

goodCadr : Int
goodCadr = cadr [1, 2]

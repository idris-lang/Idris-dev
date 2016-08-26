module FunErrTest

import Language.Reflection
import Language.Reflection.Errors
import Language.Reflection.Utils

%language ErrorReflection

total
cadr :  (xs : List a)
     -> {auto cons1 : NonEmpty xs}
     -> {auto cons2 : NonEmpty (tail xs)}
     -> a
cadr (x :: (y :: _)) {cons1=IsNonEmpty} {cons2=IsNonEmpty} = y
cadr (x :: [])       {cons1=IsNonEmpty} {cons2=IsNonEmpty} impossible
cadr []              {cons1=IsNonEmpty} {cons2=IsNonEmpty} impossible

extractList : TT -> Maybe TT
extractList (App (App neType _) lst) = Just lst
extractList t = Just t -- Nothing

total
has2elts : Err -> Maybe (List ErrorReportPart)
has2elts (CantSolveGoal tm _) = do lst <- extractList tm
                                   pure [ TextPart "Could not prove that"
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


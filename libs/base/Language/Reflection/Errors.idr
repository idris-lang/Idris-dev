module Language.Reflection.Errors

import Language.Reflection

record SourceLocation : Type where
  FileLoc : (filename : String) -> (line : Int) -> (col : Int) -> SourceLocation

%name SourceLocation loc

data Err = Msg String
         | InternalMsg String
         | CantUnify Bool TT TT Err (List (TTName, TT)) Int
              -- Int is 'score' - how much we did unify
              -- Bool indicates recoverability, True indicates more info may make
              -- unification succeed
         | InfiniteUnify TTName TT (List (TTName, TT))
         | CantConvert TT TT (List (TTName, TT))
         | CantSolveGoal TT (List (TTName, TT))
         | UnifyScope TTName TTName TT (List (TTName, TT))
         | CantInferType String
         | NonFunctionType TT TT
         | NotEquality TT TT
         | TooManyArguments TTName
         | CantIntroduce TT
         | NoSuchVariable TTName
         | NoTypeDecl TTName
         | NotInjective TT TT TT
         | CantResolve TT
         | CantResolveAlts (List String)
         | IncompleteTerm TT
         | UniverseError
         | ProgramLineComment
         | Inaccessible TTName
         | NonCollapsiblePostulate TTName
         | AlreadyDefined TTName
         | ProofSearchFail Err
         | NoRewriting TT
         | At SourceLocation Err
         | Elaborating String TTName Err
         | ProviderError String
         | LoadingFailed String Err

%name Err err, e

-- | Error reports are a list of report parts
data ErrorReportPart = TextPart String
                     | NamePart TTName
                     | TermPart TT
                     | SubReport (List ErrorReportPart)
%name ErrorReportPart part, p

-- Error reports become functions in List (String, TT) -> Err -> ErrorReport
ErrorHandler : Type
ErrorHandler = Err -> Maybe (List ErrorReportPart)

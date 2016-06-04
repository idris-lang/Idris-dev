module Language.Reflection.Errors

import Builtins

import Language.Reflection

import Prelude.Bool
import Prelude.List
import Prelude.Maybe

%access public export

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
         | WithFnType TT
         | CantMatch TT
         | NoTypeDecl TTName
         | NotInjective TT TT TT
         | CantResolve TT Err
         | InvalidTCArg TTName TT
         | CantResolveAlts (List TTName)
         | NoValidAlts (List TTName)
         | IncompleteTerm TT
         | NoEliminator String TT
         | UniverseError
         | ProgramLineComment
         | Inaccessible TTName
         | UnknownImplicit TTName TTName
         | NonCollapsiblePostulate TTName
         | AlreadyDefined TTName
         | ProofSearchFail Err
         | NoRewriting TT TT TT
         | ProviderError String
         | LoadingFailed String Err

%name Err err, e

-- Error reports become functions in List (String, TT) -> Err -> ErrorReport
ErrorHandler : Type
ErrorHandler = Err -> Maybe (List ErrorReportPart)

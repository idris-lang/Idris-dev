module Language.Reflection.Errors

import Language.Reflection

data SourceLocation = FileLoc String Int

data Err = Msg String
         | InternalMsg String
         | CantUnify Bool TT TT Err (List (TTName, TT)) Int
              -- Int is 'score' - how much we did unify
              -- Bool indicates recoverability, True indicates more info may make
              -- unification succeed
         | InfiniteUnify TTName TT (List (TTName, TT))
         | CantConvert TT TT (List (TTName, TT))
         | UnifyScope TTName TTName TT (List (TTName, TT))
         | CantInferType String
         | NonFunctionType TT TT
         | CantIntroduce TT
         | NoSuchVariable TTName
         | NoTypeDecl TTName
         | NotInjective TT TT TT
         | CantResolve TT
         | CantResolveAlts (List String)
         | IncompleteTT TT
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

data ErrorReport = Message String
                 | Name TTName
                 | Term TT


-- Error reports become functions in List (String, TT) -> Err -> ErrorReport
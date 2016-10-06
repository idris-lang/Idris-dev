module Pruviloj.Derive.Eliminators

import Language.Reflection.Utils
import Data.Vect

import public Pruviloj.Core
import Pruviloj.Internals.TyConInfo
import Pruviloj.Internals
import Pruviloj.Renamers


%access private

bindParams : TyConInfo -> Elab ()
bindParams info = traverse_ (uncurry forall) (getParams info)

||| Bind indices at new names and return a renamer that's used to
||| rewrite an application of something to their designated global
||| names
bindIndices : TyConInfo -> Elab Renamer
bindIndices info = bind' (getIndices info) noRenames
  where bind' : List (TTName, Raw) -> Renamer -> Elab Renamer
        bind' []              ren = pure ren
        bind' ((n, t) :: ixs) ren = do n' <- nameFrom n
                                       forall n' (alphaRaw ren t)
                                       bind' ixs (extend ren n n')

||| Return the renaming required to use the result type for this
||| binding of the indices
bindTarget : TyConInfo -> Elab (TTName, Renamer)
bindTarget info = do ren <- bindIndices info
                     tn <- gensym "target"
                     forall tn (alphaRaw ren $ result info)
                     pure (tn, ren)

elabMotive : TyConInfo -> Elab ()
elabMotive info = do attack
                     ren <- bindIndices info
                     x <- gensym "scrutinee"
                     forall x (alphaRaw ren $ result info)
                     fill `(Type)
                     solve -- the attack
                     solve -- the motive type hole




headsMatch : Raw -> Raw -> Bool
headsMatch x y =
  case (headName x, headName y) of
    (Just n1, Just n2) => n1 == n2
    _ => False

||| Make an induction hypothesis if one is called for
mkIh : TyConInfo -> (motiveName : TTName) -> (recArg : TTName) -> (argty, fam : Raw) -> Elab ()
mkIh info motiveName recArg argty fam =
  case !(stealBindings argty noRenames) of
    (argArgs, argRes) =>
      if headsMatch argRes fam
        then do ih <- gensym "ih"
                ihT <- newHole "ihT" `(Type)
                forall ih (Var ihT)
                focus ihT
                attack
                for_ {b=()} argArgs $ \(n, b) =>
                  forall n (binderTy b)
                let argTm : Raw = mkApp (Var recArg) (map (Var . fst) argArgs)
                argTmTy <- forget (snd !(check !getEnv argTm))
                argHoles <- apply (Var motiveName)
                                  (replicate (length (getIndices info))
                                             True ++
                                   [False])
                argH <- last argHoles
                focus argH
                fill argTm; solve
                solve -- attack
                solve -- ihT
        else pure ()

elabMethodTy : TyConInfo -> TTName -> List CtorArg -> Raw -> Raw -> Elab ()
elabMethodTy info motiveName [] res ctorApp =
  do argHoles <- apply (Var motiveName)
                       (replicate (length (getIndices info)) True ++
                        [False])
     argH <- last argHoles
     focus argH; fill ctorApp; solve
     solve
elabMethodTy info motiveName (CtorParameter arg  :: args) res ctorApp =
  elabMethodTy info motiveName args  res (RApp ctorApp (Var (name arg)))
elabMethodTy info motiveName (CtorField arg :: args) res ctorApp =
  do let n = name arg
     let t = type arg
     attack; forall n t
     mkIh info motiveName n t (result info)
     elabMethodTy info motiveName args res (RApp ctorApp (Var n))
     solve


||| Bind a method for a constructor
bindMethod : TyConInfo -> (motiveName, cn : TTName) -> List CtorArg -> Raw -> Elab ()
bindMethod info motiveName cn cargs cty =
  do n <- nameFrom cn
     h <- newHole "methTy" `(Type)
     forall n (Var h)
     focus h; elabMethodTy info motiveName cargs cty (Var cn)

getElimTy : TyConInfo -> List (TTName, List CtorArg, Raw) -> Elab Raw
getElimTy info ctors =
  do ty <- runElab `(Type) $
             do bindParams info
                (scrut, iren) <- bindTarget info
                motiveN <- gensym "P"
                motiveH <- newHole "motive" `(Type)
                forall motiveN (Var motiveH)
                focus motiveH
                elabMotive info

                for_ {b=()} ctors $ \(cn, cargs, cresty) =>
                  bindMethod info motiveN cn cargs cresty
                let ret = mkApp (Var motiveN)
                                (map (Var . fst)
                                     (getIndices info) ++
                                 [Var scrut])
                apply (alphaRaw iren ret) []
                solve
     forget (fst ty)



data ElimArg = IHArgument TTName | NormalArgument TTName

implementation Show ElimArg where
  show (IHArgument x) = "IHArgument " ++ show x
  show (NormalArgument x) = "NormalArgument " ++ show x

getElimClause : TyConInfo -> (elimn : TTName) -> (methCount : Nat) ->
                (TTName, List CtorArg, Raw) -> Nat -> Elab (FunClause Raw)
getElimClause info elimn methCount (cn, args, resTy) whichCon =
  elabPatternClause
    (do -- Establish a hole for each parameter
        for (getParams info) {b=()} $ \(n, ty) =>
          do claim n ty
             unfocus n


        -- Establish a hole for each argument to the constructor
        for {b=()} args $ \arg =>
          case arg of
            CtorParameter _ => pure ()
            CtorField arg => do claim (name arg) (type arg)
                                unfocus (name arg)

        -- Establish a hole for the scrutinee (infer type)
        scrutinee <- newHole "scrutinee" resTy


        -- Apply the eliminator to the proper holes
        let paramApp : Raw = mkApp (Var elimn) $
                             map (Var . fst) (getParams info)

        -- We leave the RHS with a function type: motive -> method* -> res
        -- to make it easier to map methods to constructors
        holes <- apply paramApp (replicate (length (getIndices info))
                                           True ++
                                 [False])
        scr <- last holes
        focus scr; fill (Var scrutinee); solve
        solve

        -- Fill the scrutinee with the concrete constructor pattern
        focus scrutinee
        apply (mkApp (Var cn) $
                 map (\x => case x of
                              CtorParameter param => Var (name param)
                              CtorField arg => Var (name arg))
                     args)
              []
        solve)
    (do motiveN <- gensym "motive"
        intro motiveN
        prevMethods <- doTimes whichCon intro1
        methN <- gensym "useThisMethod"
        intro methN
        nextMethods <- intros

        argSpec <- Foldable.concat <$>
                     for args
                         (\x =>
                            case x of
                              CtorParameter _ => pure List.Nil
                              CtorField arg =>
                                do let n = name arg
                                   let t = type arg
                                   (argArgs, argRes) <- stealBindings t noRenames
                                   if headsMatch argRes (result info) --recursive
                                     then pure [ NormalArgument n
                                               , IHArgument n
                                               ]
                                     else pure [NormalArgument n])

        argHs <- apply (Var methN) (replicate (List.length argSpec) True)
        solve

        -- Now build the recursive calls for the induction hypotheses
        for_ {a=(ElimArg, TTName)} {b=()}
             !(zipH argSpec argHs)
             (\(spec, nh) =>
                case spec of
                  NormalArgument n => do focus nh
                                         apply (Var n) []
                                         solve
                  IHArgument n =>
                    do focus nh
                       attack
                       local <- intros
                       ihHs <- apply (Var elimn) $
                         replicate (length (TyConInfo.args info)) True ++
                         [False] ++
                         replicate (S methCount) True
                       solve -- application

                       let (arg::motive::methods) = drop (length (TyConInfo.args info)) ihHs
                       focus arg

                       apply (mkApp (Var n) (map Var local)) []; solve
                       solve -- attack


                       focus motive; fill (Var motiveN); solve
                       let methodArgs : List TTName = toList prevMethods ++ [methN] ++ nextMethods
                       remaining <- zipH methods methodArgs

                       for_ {b=()} remaining $ \todo =>
                         do focus (fst todo)
                            fill (Var (snd todo))
                            solve))



  where bindLam : List (TTName, Binder Raw) -> Raw -> Raw
        bindLam [] x = x
        bindLam ((n, b)::rest) x = RBind n (Lam (binderTy b)) $ bindLam rest x

getElimClauses : TyConInfo -> (elimn : TTName) ->
                 List (TTName, List CtorArg, Raw) -> Elab (List (FunClause Raw))
getElimClauses info elimn ctors =
  let methodCount = length ctors
  in traverse (\(i, con) => getElimClause info elimn methodCount con i)
              (enumerate ctors)

export
deriveElim : (tyn, elimn : TTName) -> Elab ()
deriveElim tyn elimn =
  do -- Begin with some basic sanity checking: the type name uniquely
     -- determines a datatype
     (MkDatatype tyn tyconArgs tyconRes ctors') <- lookupDatatypeExact tyn

     info <- getTyConInfo tyconArgs (Var tyn)
     ctors <- traverse (processCtorArgs info) ctors'
     declareType $ Declare elimn [] !(getElimTy info ctors)
     clauses <- getElimClauses info elimn ctors

     defineFunction $ DefineFun elimn clauses
     pure ()


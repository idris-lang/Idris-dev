module Pruviloj.Derive.Eliminators

import Language.Reflection.Utils
import Data.Vect

import Pruviloj.Core
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
bindIndices info = bind' (getIndices info) (const Nothing)
  where bind' : List (TTName, Raw) -> Renamer -> Elab Renamer
        bind' []              ren = return ren
        bind' ((n, t) :: ixs) ren = do n' <- nameFrom n
                                       forall n' (alphaRaw ren t)
                                       bind' ixs (extend ren n n')

||| Return the renaming required to use the result type for this
||| binding of the indices
bindTarget : TyConInfo -> Elab (TTName, Renamer)
bindTarget info = do ren <- bindIndices info
                     tn <- gensym "target"
                     forall tn (alphaRaw ren $ result info)
                     return (tn, ren)

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
  case !(stealBindings argty (const Nothing)) of
    (argArgs, argRes) =>
      if headsMatch argRes fam
        then do ih <- gensym "ih"
                ihT <- newHole "ihT" `(Type)
                forall ih (Var ihT)
                focus ihT
                attack
                for_ {b=()} argArgs $ \(n, b) =>
                  forall n (getBinderTy b)
                let argTm : Raw = mkApp (Var recArg) (map (Var . fst) argArgs)
                argTmTy <- forgetTypes (snd !(check argTm))
                argHoles <- apply (Var motiveName)
                                  (replicate (length (getIndices info))
                                             (True, 0) ++
                                   [(False,1)])
                argH <- snd <$> last argHoles
                focus argH
                fill argTm; solve
                solve -- attack
                solve -- ihT
        else return ()

elabMethodTy : TyConInfo -> TTName -> List CtorArg -> Raw -> Raw -> Elab ()
elabMethodTy info motiveName [] res ctorApp =
  do argHoles <- apply (Var motiveName)
                       (replicate (length (getIndices info)) (True, 0) ++
                        [(False, 1)])
     argH <- snd <$> last argHoles
     focus argH; fill ctorApp; solve
     solve
elabMethodTy info motiveName (CtorParameter arg  :: args) res ctorApp =
  elabMethodTy info motiveName args  res (RApp ctorApp (Var (argName arg)))
elabMethodTy info motiveName (CtorField arg :: args) res ctorApp =
  do let n = argName arg
     let t = argTy arg
     attack; forall n t
     mkIh info motiveName n t (result info)
     elabMethodTy info motiveName args res (RApp ctorApp (Var n))
     solve



elabMethod : TyConInfo -> (motiveName, ctorN : TTName) -> List CtorArg -> Raw -> Elab ()
elabMethod info motiveName ctorN ctorArgs resTy =
  do elabMethodTy info motiveName ctorArgs resTy (Var ctorN)


||| Bind a method for a constructor
bindMethod : TyConInfo -> (motiveName, cn : TTName) -> List CtorArg -> Raw -> Elab ()
bindMethod info motiveName cn cargs cty =
  do n <- nameFrom cn
     h <- newHole "methTy" `(Type)
     forall n (Var h)
     focus h; elabMethod info motiveName cn cargs cty

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
     forgetTypes (fst ty)



data ElimArg = IHArgument TTName | NormalArgument TTName

instance Show ElimArg where
  show (IHArgument x) = "IHArgument " ++ show x
  show (NormalArgument x) = "NormalArgument " ++ show x

getElimClause : TyConInfo -> (elimn : TTName) -> (methCount : Nat) ->
                (TTName, List CtorArg, Raw) -> Nat -> Elab FunClause
getElimClause info elimn methCount (cn, args, resTy) whichCon =
  elabPatternClause
    (do -- Establish a hole for each parameter
        for (getParams info) {b=()} $ \(n, ty) =>
          do claim n ty
             unfocus n


        -- Establish a hole for each argument to the constructor
        for {b=()} args $ \arg =>
          case arg of
            CtorParameter _ => return ()
            CtorField arg => do claim (argName arg) (argTy arg)
                                unfocus (argName arg)

        -- Establish a hole for the scrutinee (infer type)
        scrutinee <- newHole "scrutinee" resTy


        -- Apply the eliminator to the proper holes
        let paramApp : Raw = mkApp (Var elimn) $
                             map (Var . fst) (getParams info)

        -- We leave the RHS with a function type: motive -> method* -> res
        -- to make it easier to map methods to constructors
        holes <- apply paramApp (replicate (length (getIndices info))
                                           (True, 0) ++
                                 [(False, 1)])
        scr <- snd <$> last holes
        focus scr; fill (Var scrutinee); solve
        solve

        -- Fill the scrutinee with the concrete constructor pattern
        focus scrutinee
        apply (mkApp (Var cn) $
                 map (\x => case x of
                              CtorParameter param => Var (argName param)
                              CtorField arg => Var (argName arg))
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
                              CtorParameter _ => return List.Nil
                              CtorField arg =>
                                do let n = argName arg
                                   let t = argTy arg
                                   (argArgs, argRes) <- stealBindings t (const Nothing)
                                   if headsMatch argRes (result info) --recursive
                                     then return [ NormalArgument n
                                                 , IHArgument n
                                                 ]
                                     else return [NormalArgument n])

        argHs <- apply (Var methN) (replicate (List.length argSpec) (True, 0))
        solve

        -- Now build the recursive calls for the induction hypotheses
        for_ {a=(ElimArg, TTName)} {b=()}
             !(zipH argSpec (map snd argHs))
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
                         replicate (length (TyConInfo.args info)) (True, 0) ++
                         [(False, 1)] ++
                         replicate (S methCount) (True, 0)
                       solve -- application

                       let (arg::motive::methods) = map snd $ drop (length (TyConInfo.args info)) ihHs
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
        bindLam ((n, b)::rest) x = RBind n (Lam (getBinderTy b)) $ bindLam rest x

getElimClauses : TyConInfo -> (elimn : TTName) ->
                 List (TTName, List CtorArg, Raw) -> Elab (List FunClause)
getElimClauses info elimn ctors =
  let methodCount = length ctors
  in traverse (\(i, con) => getElimClause info elimn methodCount con i)
              (enumerate ctors)

instance Show FunClause where
  show (MkFunClause x y) = "(MkFunClause " ++ show x ++ " " ++ show y ++ ")"

abstract
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
     return ()


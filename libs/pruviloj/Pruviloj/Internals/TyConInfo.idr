module Pruviloj.Internals.TyConInfo

import Pruviloj.Core
import Pruviloj.Internals
import Pruviloj.Renamers

import Language.Reflection.Utils

%access public export

||| A representation of a type constructor in which all argument names
||| are made unique and they are separated into params and then
||| indices.
record TyConInfo where
  constructor MkTyConInfo
  ||| Invariant: the names of the args have been made unique
  args : List TyConArg
  ||| The type constructor, applied to its arguments
  result : Raw

%name TyConInfo info

getParams : TyConInfo -> List (TTName, Raw)
getParams info = mapMaybe param (args info)
  where param : TyConArg -> Maybe (TTName, Raw)
        param (TyConParameter a) = Just (name a, type a)
        param _ = Nothing

getIndices : TyConInfo -> List (TTName, Raw)
getIndices info = mapMaybe index (args info)
  where index : TyConArg -> Maybe (TTName, Raw)
        index (TyConIndex a) = Just (name a, type a)
        index _ = Nothing

||| Rename a bound variable across a telescope
renameIn : (from, to : TTName) -> List (TTName, Raw) -> List (TTName, Raw)
renameIn from to [] = []
renameIn from to ((n, ty)::tele) =
    (n, alphaRaw (rename from to) ty) ::
      if from == n
        then tele
        else renameIn from to tele

||| Rename a free variable in type constructor info (used to implement
||| alpha-conversion for unique binder names, hence the odd name)
alphaTyConInfo : (TTName -> Maybe TTName) -> TyConInfo -> TyConInfo
alphaTyConInfo ren (MkTyConInfo [] res) = MkTyConInfo [] (alphaRaw ren res)
alphaTyConInfo ren (MkTyConInfo (tcArg::tcArgs) res) =
  let MkTyConInfo tcArgs' res' = alphaTyConInfo (restrict ren (tyConArgName tcArg)) (MkTyConInfo tcArgs res)
      tcArg' = updateTyConArgTy (alphaRaw ren) tcArg
  in MkTyConInfo (tcArg'::tcArgs') res'

getTyConInfo' : List TyConArg -> Raw -> (TTName -> Maybe TTName) -> Elab TyConInfo
getTyConInfo' [] res _ = pure (MkTyConInfo [] res)
getTyConInfo' (tcArg::tcArgs) res ren =
  do let n = tyConArgName tcArg
     n' <- nameFrom n
     let ren' = extend ren n n'
     -- n' is globally unique so we don't worry about scope
     next <- getTyConInfo' tcArgs (RApp res (Var n')) ren'
     pure $ alphaTyConInfo ren' $
       record {args = setTyConArgName tcArg n' :: args next} next

getTyConInfo : List TyConArg -> Raw -> Elab TyConInfo
getTyConInfo args res = getTyConInfo' args res (const Nothing)

||| Convert the parameter names in a constructor to their global unique versions
processCtorArgs : TyConInfo -> (TTName, List CtorArg, Raw) -> Elab (TTName, List CtorArg, Raw)
processCtorArgs info (cn, cargs, resTy) =
    do (args', ty') <- convert' (const Nothing) cargs resTy info
       pure (cn, args', ty')
  where
    ||| Find the name that was assigned to a given parameter
    ||| by comparing positions in the TyConInfo
    findParam : TTName -> List Raw -> List TyConArg -> Elab TTName
    findParam paramN (Var n :: args) (TyConParameter a :: tcArgs) =
      if n == paramN
        then pure (name a)
        else findParam paramN args tcArgs
    findParam paramN (_ :: args) (_ :: tcArgs) =
      findParam paramN args tcArgs
    findParam paramN _ _ = fail [ TextPart "Parameter"
                                , NamePart paramN
                                , TextPart "not found."
                                ]

    convert' : (TTName -> Maybe TTName) ->
               List CtorArg -> Raw ->
               TyConInfo -> Elab (List CtorArg, Raw)
    convert' subst [] ty info = pure ([], alphaRaw subst ty)
    convert' subst (CtorField a :: args) ty info =
      do n' <- nameFrom (name a)
         let a' = record {
                    name = n'
                  , type = alphaRaw subst (type a)
                  } a
         let subst' = extend subst (name a) n'
         (args', ty') <- convert' subst' args ty info
         pure (CtorField a' :: args', ty')
    convert' subst (CtorParameter a :: ctorArgs) ty info =
      do n' <- findParam (name a) (snd (unApply ty)) (args info)
         let a' = record {
                    name = n'
                  , type = alphaRaw subst (type a)
                  } a
         let subst' = extend subst (name a) n'
         (args', ty') <- convert' subst' ctorArgs ty info
         pure (CtorParameter a' :: args', ty')

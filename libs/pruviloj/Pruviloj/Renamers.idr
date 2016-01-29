module Pruviloj.Renamers

import Language.Reflection.Utils

%access public export

||| A renamer keeps track of names to be substituted
Renamer : Type
Renamer = TTName -> Maybe TTName

||| A renamer that renames nothing
noRenames : Renamer
noRenames = const Nothing

||| Cause a renamer to forget a renaming
restrict : Renamer -> TTName -> Renamer
restrict f n n' = if n == n' then Nothing else f n'

||| Extend a renamer with a new renaming
extend : Renamer -> TTName -> TTName -> Renamer
extend f n n' n'' = if n'' == n then Just n' else f n''

||| Create a new renamer
|||
||| @ from the old name
||| @ to the new name
rename : (from, to : TTName) -> Renamer
rename from to = extend noRenames from to

||| Alpha-convert `Raw` terms
||| @ subst a renamer
partial
alphaRaw : (subst : Renamer) -> Raw -> Raw
alphaRaw subst (Var n) with (subst n)
  alphaRaw subst (Var n) | Nothing = Var n
  alphaRaw subst (Var n) | Just n' = Var n'
alphaRaw subst (RBind n b tm) =
  let subst' = restrict subst n
      b' = map (alphaRaw subst) b
  in RBind n b' (alphaRaw subst' tm)
alphaRaw subst (RApp tm tm') = RApp (alphaRaw subst tm) (alphaRaw subst tm')
alphaRaw subst RType = RType
alphaRaw subst (RUType x) = RUType x
alphaRaw subst (RConstant c) = RConstant c

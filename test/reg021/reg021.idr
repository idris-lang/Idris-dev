module Main

%default total

data Ty = TyBool

data Id a = I a

interpTy : Ty -> Type
interpTy TyBool = Id Bool

data Term : Ty -> Type where
  TLit : Bool -> Term TyBool
  TNot : Term TyBool -> Term TyBool

map : (a -> b) -> Id a -> Id b
map f (I x) = I (f x)

interp : Term t -> interpTy t
interp (TLit x) = I x
interp (TNot x) = map not (interp x)


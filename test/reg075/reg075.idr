module PDefs

%access public export

data Common = MkCommon

data MTy = MMODEL | MELEM | MLINK
data Model : MTy -> Type where
  MkModel : Model MMODEL
  MLink : Common -> Model MELEM -> Model MELEM -> Model MLINK
  MElem : String -> Model MELEM

data BTy = BELEM | BMODEL
data Bar : Model ty -> BTy -> Type where
  BElem : (name : String) -> Bar (MElem name) BELEM
  BModel : Bar (MkModel) BMODEL

data Pred : Bar g BELEM -> Bar m BMODEL -> Type where

isValid : (f : Bar g BELEM) -> (p : Bar m BMODEL) -> Dec (Pred f p)
isValid p = ?as

data FTy = FELEM | FLINK

data Foo : Bar m BMODEL -> Model ty -> FTy -> Type where
   FElem : (name : String) -> Foo p (MElem name) FELEM

   FLink : (a : Foo p x FELEM)
           -> (c : Common)
           -> (f : Bar g BELEM)
           -> {auto prf : isValid f p = Yes prf'}
           -> Foo p (MLink c x g) FLINK


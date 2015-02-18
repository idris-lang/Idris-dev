module Language.Reflection.Tactical

import Builtins
import Prelude.Applicative
import Prelude.Functor
import Prelude.List
import Prelude.Maybe
import Prelude.Monad
import Language.Reflection

data Tactical : Type -> Type where
  -- obligatory control stuff
  PureTactical : a -> Tactical a
  BindTactical : {a, b : Type} -> Tactical a -> (a -> Tactical b) -> Tactical b

  Try : {a : Type} -> Tactical a -> Tactical a -> Tactical a
  Skip : Tactical ()
  Fail : {a : Type} -> List ErrorReportPart -> Tactical a

  Env : Tactical (List (TTName, Binder TT))
  Goal : Tactical (TTName, TT)
  Holes : Tactical (List TTName)
  Guess : Tactical (Maybe TT)

  Forget : TT -> Tactical Raw

  Gensym : String -> Tactical TTName

  Solve : Tactical ()
  Fill : Raw -> Tactical ()
  Focus : TTName -> Tactical ()
  Unfocus : TTName -> Tactical ()
  Attack : Tactical ()

  Claim : TTName -> Raw -> Tactical ()


instance Functor Tactical where
  map f t = BindTactical t (\x => PureTactical (f x))

instance Applicative Tactical where
  pure x = PureTactical x
  f <$> x = BindTactical f $ \g =>
            BindTactical x $ \y =>
            PureTactical   $ g y

instance Alternative Tactical where
  empty   = Fail [TextPart "empty"]
  x <|> y = Try x y

instance Monad Tactical where
  x >>= f = BindTactical x f


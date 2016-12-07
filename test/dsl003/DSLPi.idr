module DSLPi

import Data.Fin
import Data.Vect

%language DSLNotation

data Ty = BOOL | INT | UNIT | ARR Ty Ty

arr_ : _ -> Ty -> Ty -> Ty
arr_ _ = ARR

dsl simple_type
  pi = arr_

test1 : simple_type (BOOL -> INT -> UNIT) = BOOL `ARR` (INT `ARR` UNIT)
test1 = Refl

using (vars : Vect n Ty)
  infix 2 ===

  data Expr : Vect n Ty -> Ty -> Type where
    Var : (i : Fin n) -> Expr vars (index i vars)
    (===) : Expr vars t -> Expr vars t -> Expr vars BOOL

  data Spec : Vect n Ty -> Type where
    ForAll : (t : Ty) -> Spec (t :: vars) -> Spec vars
    ItHolds : Expr vars BOOL -> Spec vars

  implicit exprSpec : Expr vars BOOL -> Spec vars
  exprSpec = ItHolds

  forall_ : _ -> (t : Ty) -> Spec (t :: vars) -> Spec vars
  forall_ _ = ForAll

dsl specs
  pi = forall_
  variable = Var
  index_first = FZ
  index_next = FS

test2 : Spec []
test2 = specs ((x, y : INT) -> x === y)

test3 : Spec []
test3 = ForAll INT . ForAll INT . ItHolds $ Var (FS FZ) === Var FZ

test4 : DSLPi.test2 = DSLPi.test3
test4 = Refl

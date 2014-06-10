module DSLPi

data Ty = BOOL | INT | UNIT | ARR Ty Ty

dsl simple_type
  pi = ARR

test1 : simple_type (BOOL -> INT -> UNIT) = BOOL `ARR` (INT `ARR` UNIT)
test1 = refl

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

dsl specs
  pi = ForAll
  variable = Var
  index_first = fZ
  index_next = fS

test2 : Spec []
test2 = specs ((x, y : INT) -> x === y)

test3 : Spec []
test3 = ForAll INT . ForAll INT . ItHolds $ Var (fS fZ) === Var fZ

test4 : test2 = test3
test4 = refl

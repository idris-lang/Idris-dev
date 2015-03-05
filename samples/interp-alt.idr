module main

data Ty = TyInt | TyBool| TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy (TyFun s t) = interpTy s -> interpTy t

using (G : Vect n Ty)

  data Env : Vect n Ty -> Type where
      Nil  : Env Nil
      (::) : interpTy a -> Env G -> Env (a :: G)

--   data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
--       stop : HasType FZ (t :: G) t
--       pop  : HasType k G t -> HasType (FS k) (u :: G) t

  lookup : (i:Fin n) -> Env G -> interpTy (index i G)
  lookup FZ     (x :: xs) = x
  lookup (FS i) (x :: xs) = lookup i xs

  data Expr : Vect n Ty -> Ty -> Type where
      Var : (i : Fin n) -> Expr G (index i G)
      Val : (x : Int) -> Expr G TyInt
      Lam : Expr (a :: G) t -> Expr G (TyFun a t)
      App : Expr G (TyFun a t) -> Expr G a -> Expr G t
      Op  : (interpTy a -> interpTy b -> interpTy c) -> Expr G a -> Expr G b ->
            Expr G c
      If  : Expr G TyBool -> Expr G a -> Expr G a -> Expr G a
      Bind : Expr G a -> (interpTy a -> Expr G b) -> Expr G b

  interp : Env G -> {static} Expr G t -> interpTy t
  interp env (Var i)     = lookup i env
  interp env (Val x)     = x
  interp env (Lam sc)    = \x => interp (x :: env) sc
  interp env (App f s)   = (interp env f) (interp env s)
  interp env (Op op x y) = op (interp env x) (interp env y)
  interp env (If x t e)  = if (interp env x) then (interp env t) else (interp env e)
  interp env (Bind v f)  = interp env (f (interp env v))

  eId : Expr G (TyFun TyInt TyInt)
  eId = Lam (Var FZ)

  eTEST : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eTEST = Lam (Lam (Var (FS FZ)))

  eAdd : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eAdd = Lam (Lam (Op prim__addInt (Var FZ) (Var (FS FZ))))

--   eDouble : Expr G (TyFun TyInt TyInt)
--   eDouble = Lam (App (App (Lam (Lam (Op' (+) (Var FZ) (Var (FS FZ))))) (Var FZ)) (Var FZ))

  eDouble : Expr G (TyFun TyInt TyInt)
  eDouble = Lam (App (App eAdd (Var FZ)) (Var FZ))

  app : |(f : Expr G (TyFun a t)) -> Expr G a -> Expr G t
  app = \f, a => App f a

  eFac : Expr G (TyFun TyInt TyInt)
  eFac = Lam (If (Op (==) (Var FZ) (Val 0))
                 (Val 1) (Op (*) (app eFac (Op (-) (Var FZ) (Val 1))) (Var FZ)))

  -- Exercise elaborator: Complicated way of doing \x y => x*4 + y*2

  eProg : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eProg = Lam (Lam (Bind (App eDouble (Var (FS FZ)))
              (\x => Bind (App eDouble (Var FZ))
              (\y => Bind (App eDouble (Val x))
              (\z => App (App eAdd (Val y)) (Val z))))))

test : Int
test = interp [] eProg 2 2

testFac : Int
testFac = interp [] eFac 4

main : IO ()
main = do printLn test
          printLn testFac

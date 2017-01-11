module Main

import Data.Vect
import Data.Fin

%language DSLNotation

data Ty = TyInt | TyBool| TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy (TyFun s t) = interpTy s -> interpTy t

using (G : Vect n Ty)

  data Env : Vect n Ty -> Type where
      Nil  : Env Nil
      (::) : interpTy a -> Env G -> Env (a :: G)

  data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
      Stop : HasType FZ (t :: G) t
      Pop  : HasType k G t -> HasType (FS k) (u :: G) t

  lookup : HasType i G t -> Env G -> interpTy t
  lookup Stop    (x :: xs) = x
  lookup (Pop k) (x :: xs) = lookup k xs
  lookup Stop    [] impossible

  data Expr : Vect n Ty -> Ty -> Type where
      Var : HasType i G t -> Expr G t
      Val : (x : Int) -> Expr G TyInt
      Lam : Expr (a :: G) t -> Expr G (TyFun a t)
      App : Lazy (Expr G (TyFun a t)) -> Expr G a -> Expr G t
      Op  : (interpTy a -> interpTy b -> interpTy c) -> Expr G a -> Expr G b ->
            Expr G c
      If  : Expr G TyBool -> Expr G a -> Expr G a -> Expr G a
      Bind : Expr G a -> (interpTy a -> Expr G b) -> Expr G b

  %static
  lam_ : TTName -> Expr (a :: G) t -> Expr G (TyFun a t)
  lam_ _ = Lam

  dsl expr
      lambda = lam_
      variable = Var
      index_first = Stop
      index_next = Pop

  total
  interp : Env G -> %static (e : Expr G t) -> interpTy t
  interp env (Var i)     = lookup i env
  interp env (Val x)     = x
  interp env (Lam sc)    = \x => interp (x :: env) sc
  interp env (App f s)   = (interp env f) (interp env s)
  interp env (Op op x y) = op (interp env x) (interp env y)
  interp env (If x t e)  = if interp env x then interp env t else interp env e
  interp env (Bind v f)  = interp env (f (interp env v))

  eId : Expr G (TyFun TyInt TyInt)
  eId = expr (\x => x)

  eTEST : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eTEST = expr (\x, y => y)

  eAdd : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eAdd = expr (\x, y => Op (+) x y)

--   eDouble : Expr G (TyFun TyInt TyInt)
--   eDouble = Lam (App (App (Lam (Lam (Op' (+) (Var FZ) (Var (FS FZ))))) (Var FZ)) (Var FZ))

  eDouble : Expr G (TyFun TyInt TyInt)
  eDouble = expr (\x => App (App eAdd x) (Var Stop))

--   app : Lazy (Expr G (TyFun a t)) -> Expr G a -> Expr G t
--   app = \f, a => App (Force f) a

  eFac : Expr G (TyFun TyInt TyInt)
  eFac = expr (\x => If (Op (==) x (Val 0))
                 (Val 1)
                 (Op (*) (App eFac (Op (-) x (Val 1))) x))

  -- Exercise elaborator: Complicated way of doing \x y => x*4 + y*2

  eProg : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eProg = Lam (Lam
                    (Bind (App eDouble (Var (Pop Stop)))
              (\x => Bind (App eDouble (Var Stop))
              (\y => Bind (App eDouble (Val x))
              (\z => App (App eAdd (Val y)) (Val z))))))

test : Int
test = interp [] eProg 2 2

testFac : Int
testFac = interp [] eFac 4

testEnv : Int -> Env [TyInt,TyInt]
testEnv x = [x,x]

main : IO ()
main = do { printLn testFac
            printLn test }



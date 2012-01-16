module main

data Ty = TyInt | TyBool| TyFun Ty Ty

interpTy : Ty -> Set
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy (TyFun s t) = interpTy s -> interpTy t

using (G : Vect Ty n)

  data Env : Vect Ty n -> Set where
      Nil  : Env Nil
      (::) : interpTy a -> Env G -> Env (a :: G)

--   data HasType : (i : Fin n) -> Vect Ty n -> Ty -> Set where
--       stop : HasType fO (t :: G) t
--       pop  : HasType k G t -> HasType (fS k) (u :: G) t

  lookup : (i:Fin n) -> Env G -> interpTy (lookup i G)
  lookup fO     (x :: xs) = x
  lookup (fS i) (x :: xs) = lookup i xs

  data Expr : Vect Ty n -> Ty -> Set where
      Var : (i : Fin n) -> Expr G (lookup i G)
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
  eId = Lam (Var fO)

  eTEST : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eTEST = Lam (Lam (Var (fS fO)))

  eAdd : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eAdd = Lam (Lam (Op prim__addInt (Var fO) (Var (fS fO))))
  
--   eDouble : Expr G (TyFun TyInt TyInt)
--   eDouble = Lam (App (App (Lam (Lam (Op' (+) (Var fO) (Var (fS fO))))) (Var fO)) (Var fO))
  
  eDouble : Expr G (TyFun TyInt TyInt)
  eDouble = Lam (App (App eAdd (Var fO)) (Var fO))
 
  app : |(f : Expr G (TyFun a t)) -> Expr G a -> Expr G t
  app = \f, a => App f a

  eFac : Expr G (TyFun TyInt TyInt)
  eFac = Lam (If (Op (==) (Var fO) (Val 0))
                 (Val 1) (Op (*) (app eFac (Op (-) (Var fO) (Val 1))) (Var fO)))

  -- Exercise elaborator: Complicated way of doing \x y => x*4 + y*2
  
  eProg : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eProg = Lam (Lam (Bind (App eDouble (Var (fS fO)))
              (\x => Bind (App eDouble (Var fO))
              (\y => Bind (App eDouble (Val x))
              (\z => App (App eAdd (Val y)) (Val z))))))

test : Int
test = interp [] eProg 2 2

testFac : Int
testFac = interp [] eFac 4

main : IO ()
main = do print test
          print testFac

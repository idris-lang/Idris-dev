module Main

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
      stop : HasType fZ (t :: G) t
      pop  : HasType k G t -> HasType (fS k) (u :: G) t

  lookup : HasType i G t -> Env G -> interpTy t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs
  lookup stop    [] impossible

  data Expr : Vect n Ty -> Ty -> Type where
      Var : HasType i G t -> Expr G t
      Val : (x : Int) -> Expr G TyInt
      Lam : Expr (a :: G) t -> Expr G (TyFun a t)
      App : Expr G (TyFun a t) -> Expr G a -> Expr G t
      Op  : (interpTy a -> interpTy b -> interpTy c) -> Expr G a -> Expr G b -> 
            Expr G c
      If  : Expr G TyBool -> Expr G a -> Expr G a -> Expr G a
      Bind : Expr G a -> (interpTy a -> Expr G b) -> Expr G b
 
  dsl expr
      lambda = Lam
      variable = Var
      index_first = stop
      index_next = pop

  interp : Env G -> {static} Expr G t -> interpTy t
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
--   eDouble = Lam (App (App (Lam (Lam (Op' (+) (Var fZ) (Var (fS fZ))))) (Var fZ)) (Var fZ))
  
  eDouble : Expr G (TyFun TyInt TyInt)
  eDouble = expr (\x => App (App eAdd x) (Var stop))
 
  app : |(f : Expr G (TyFun a t)) -> Expr G a -> Expr G t
  app = \f, a => App f a

  eFac : Expr G (TyFun TyInt TyInt)
  eFac = expr (\x => If (Op (==) x (Val 0))
                 (Val 1) 
                 (Op (*) (app eFac (Op (-) x (Val 1))) x))

  -- Exercise elaborator: Complicated way of doing \x y => x*4 + y*2
  
  eProg : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eProg = Lam (Lam 
                    (Bind (App eDouble (Var (pop stop)))
              (\x => Bind (App eDouble (Var stop))
              (\y => Bind (App eDouble (Val x))
              (\z => App (App eAdd (Val y)) (Val z))))))

test : Int
test = interp [] eProg 2 2

testFac : Int
testFac = interp [] eFac 4

testEnv : Int -> Env [TyInt,TyInt]
testEnv x = [x,x]

main : UnsafeIO ()
main = do { print testFac
            print test }




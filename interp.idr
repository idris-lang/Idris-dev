data Ty = TyNat | TyFun Ty Ty;

interpTy : Ty -> Set;
interpTy TyNat       = Nat;
interpTy (TyFun s t) = interpTy s -> interpTy t;

using (G : Vect Ty n) {

  data Env : Vect Ty n -> Set where
      Empty  : Env VNil
    | Extend : interpTy a -> Env G -> Env (a :: G);

  envLookup : (i : Fin n) -> Env G -> interpTy (vlookup i G);
  envLookup fO     (Extend x xs) = x;
  envLookup (fS i) (Extend x xs) = envLookup i xs;
  
  data Expr : Vect Ty n -> Ty -> Set where
      Var : (i : Fin n) -> Expr G (vlookup i G)
    | Val : Nat -> Expr G TyNat
    | Lam : Expr (a :: G) t -> Expr G (TyFun a t)
    | App : Expr G (TyFun a t) -> Expr G a -> Expr G t
    | Add : Expr G TyNat -> Expr G TyNat -> Expr G TyNat
    | Bind : Expr G a -> (interpTy a -> Expr G b) -> Expr G b;
  
  interp : Env G -> Expr G t -> interpTy t;
  interp env (Var i)    = envLookup i env;
  interp env (Val x)    = x;
  interp env (Lam sc)   = \x => interp (Extend x env) sc;
  interp env (App f s)  = (interp env f) (interp env s);
  interp env (Add x y)  = plus (interp env x) (interp env y);
  interp env (Bind v f) = interp env (f (interp env v));
  
  eAdd : Expr G (TyFun TyNat (TyFun TyNat TyNat));
  eAdd = Lam (Lam (Add (Var fO) (Var (fS fO))));
  
  eDouble : Expr G (TyFun TyNat TyNat);
  eDouble = Lam (App (App (Lam (Lam (Add (Var fO) (Var (fS fO))))) (Var fO)) (Var fO));
  
  eDouble' : Expr G (TyFun TyNat TyNat);
  eDouble' = Lam (App (App eAdd (Var fO)) (Var fO));
  
  -- Exercise elaborator: Complicated way of doing \x y => x*4 + y*2
  
  eProg : Expr G (TyFun TyNat (TyFun TyNat TyNat));
  eProg = Lam (Lam 
                    (Bind (App eDouble (Var (fS fO)))
              (\x => Bind (App eDouble (Var fO))
              (\y => Bind (App eDouble (Val x))
              (\z => App (App eAdd (Val y)) (Val z))))));
}

test : Nat;
test = interp Empty eProg (S (S O)) (S (S O));

natToStr : Nat -> String;
natToStr O = "O";
natToStr (S k) = "s" ++ natToStr k;

main : IO ();
main = putStrLn (natToStr test);


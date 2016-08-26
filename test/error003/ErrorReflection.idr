module Main

import Language.Reflection
import Language.Reflection.Errors
import Language.Reflection.Utils
import Data.Vect

%language ErrorReflection

-- Well-typed terms

data Ty = TUnit | TFun Ty Ty

implementation Show Ty where
  show TUnit = "()"
  show (TFun t1 t2) = "(" ++ show t1 ++ " => " ++ show t2 ++ ")"

using (n : Nat, G : Vect n Ty)
  data HasType : Vect n Ty -> Ty -> Type where
    Here : HasType (t::G) t
    There : HasType G t -> HasType (t' :: G) t

  data Tm : Vect n Ty -> Ty -> Type where
    U : Tm G TUnit
    Var : HasType G t -> Tm G t
    Lam : Tm (t :: G) t' -> Tm G (TFun t t')
    App : Tm G (TFun t t') -> Tm G t -> Tm G t'

-- Extract the type from a reflected term type

namespace ErrorReports
  data Ty' = TUnit
           | TFun Ty' Ty'
           | TVar Int String -- To show in unification failures

  implementation Show Ty' where
    show TUnit = "()"
    show (TFun x y) = "(" ++ show x ++ " => " ++ show y ++ ")"
    show (TVar i n) = n ++ "(" ++ cast i ++ ")"

getTmTy : TT -> Maybe TT
getTmTy (App (App (App (P (TCon _ _) (NS (UN "Tm") _) _) _) _) ty) = Just ty
getTmTy _ = Nothing


reifyTy : TT -> Maybe Ty'
reifyTy (P (DCon _ _) (NS (UN "TUnit") _) _) = Just TUnit
reifyTy (App (App (P (DCon _ _) (NS (UN "TFun") _) _) t1) t2) = do ty1 <- reifyTy t1
                                                                   ty2 <- reifyTy t2
                                                                   pure $ TFun ty1 ty2
reifyTy (P _ (MN i n) _) = Just (TVar i n)
reifyTy _ = Nothing

-- Friendly error reporting

total %error_handler
dslerr : Err -> Maybe (List ErrorReportPart)
dslerr (CantUnify _ tm1 tm2 _ _ _) = do tm1' <- getTmTy tm1
                                        tm2' <- getTmTy tm2
                                        ty1 <- reifyTy tm1'
                                        ty2 <- reifyTy tm2'
                                        Just [TextPart $ "DSL type error: " ++ (show ty1) ++ " doesn't match " ++(show ty2)]
dslerr _ = Nothing


-- Report the error
bad : Tm [] TUnit
bad = Lam (Var Here)


import Language.Reflection.Utils
import Pruviloj.Core

rename : TTName -> TTName -> Raw -> Raw
rename old new (RBind name b body) = RBind name (map (rename old new) b) (rename old new body)
rename old new (RApp f arg) = RApp (rename old new f) (rename old new arg)
rename old new (Var n) = if n == old then Var new else Var n
rename old new tm = tm

roundtrip : TTName -> TTName -> Elab ()
roundtrip old new = do
  DefineFun _ clauses <- lookupFunDefnExact old
  clauses' <- for clauses (\(MkFunClause lhs rhs) => do
    lhs' <- rename old new <$> forget lhs
    rhs' <- rename old new <$> forget rhs
    pure $ MkFunClause lhs' rhs')
  defineFunction (DefineFun new clauses')

plus' : Nat -> Nat -> Nat
%runElab (roundtrip `{plus} `{plus'})

total
p : (a : Nat) -> (b : Nat) -> plus a b = plus' a b
p Z right = Refl
p (S left) right = Refl

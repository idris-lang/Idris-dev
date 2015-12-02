import Language.Reflection.Utils
import Pruviloj.Core

forgotToNatAndRename : TTName -> TTName -> Raw -> Raw
forgotToNatAndRename old new (RBind name b body) = RBind name (map (forgotToNatAndRename old new) b) (forgotToNatAndRename old new body)
forgotToNatAndRename old new (RApp f arg) = RApp (forgotToNatAndRename old new f) (forgotToNatAndRename old new arg)
forgotToNatAndRename old new (RConstant Forgot) = Var `{Nat}
forgotToNatAndRename old new (Var n) = if n == old then Var new else Var n
forgotToNatAndRename old new tm = tm

roundtrip : TTName -> TTName -> Elab ()
roundtrip old new = do
  DefineFun _ clauses <- lookupFunDefnExact old
  clauses' <- for clauses (\(MkFunClause lhs rhs) => do
    lhs' <- forgotToNatAndRename old new <$> forget lhs
    rhs' <- forgotToNatAndRename old new <$> forget rhs
    pure $ MkFunClause lhs' rhs')
  defineFunction (DefineFun new clauses')

plus' : Nat -> Nat -> Nat
%runElab (roundtrip `{plus} `{plus'})

total
p : (a : Nat) -> (b : Nat) -> plus a b = plus' a b
p Z right = Refl
p (S left) right = Refl

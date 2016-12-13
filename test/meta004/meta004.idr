import Data.Fin
import Language.Reflection.Utils
import Pruviloj.Core

%language ElabReflection

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


-- Test handling of impossible clauses in function definitions
foo : Fin Z -> Nat
bar : Nat -> Fin Z

doit : Elab ()
doit = defineFunction $
          DefineFun `{foo} [MkImpossibleClause
                             (RBind `{{n}}
                               (PVar (Var `{Nat}))
                               (RApp (Var `{foo})
                                 (RApp (Var `{FZ}) (Var `{{n}}))))]

domore : Elab ()
domore = defineFunction $
            DefineFun `{foo} [MkImpossibleClause $
                                RBind `{{k}} (PVar `(Nat)) $
                                  RApp (Var `{bar}) (Var `{{k}})]

%runElab doit
%runElab domore

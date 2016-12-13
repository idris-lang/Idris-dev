module DataDef

%language ElabReflection

foo : Elab ()
foo = do declareDatatype $ Declare `{{DataDef.N}} [MkFunArg `{{n}} `(Nat) Explicit NotErased] `(Type)
         defineDatatype $ DefineDatatype `{{DataDef.N}} [
                            Constructor `{{MkN}} [MkFunArg `{{x}} `(Nat) Implicit NotErased] (RApp (Var `{{DataDef.N}}) (Var `{{x}})),
                            Constructor `{{MkN'}} [MkFunArg `{{x}} `(Nat) Explicit NotErased] (RApp (Var `{{DataDef.N}}) (RApp (Var `{S}) (Var `{{x}})))
                          ]
%runElab foo

one : N 1
one = MkN

two : N 2
two = MkN' 1


-- mutual
--   data U : Type where
--     Base : U
--     Pi : (code : U) -> (el code -> U) -> U
--   el : U -> Type
--   el Base = Bool
--   el (Pi code body) = (x : el code) -> el (body x)



mkU : Elab ()
mkU = do let U = `{{DataDef.U}}
         let el = `{{DataDef.el}}
         declareDatatype $ Declare U [] `(Type)
         declareType $ Declare el [MkFunArg `{{code}} (Var U) Explicit NotErased] `(Type)
         defineDatatype $ DefineDatatype U [
                            Constructor `{{Base}} [] (Var U),
                            Constructor `{{Pi}}
                                        [MkFunArg `{{code}} (Var U) Explicit NotErased,
                                         MkFunArg `{{body}} `(~(RApp (Var el) (Var `{{code}})) -> ~(Var U)) Explicit NotErased]
                                        (Var U)
                          ]
         defineFunction $ DefineFun el [
                            MkFunClause (RBind `{{code}} (PVar (Var U))
                                           (RBind `{{body}} (PVar `(~(RApp (Var el) (Var `{{code}})) -> ~(Var U)))
                                              (RApp (Var el)
                                                    (RApp (RApp (Var `{{DataDef.Pi}})
                                                                (Var `{{code}}))
                                                          (Var `{{body}})))))
                                        (RBind `{{code}} (PVar (Var U))
                                           (RBind `{{body}} (PVar `(~(RApp (Var el) (Var `{{code}})) -> ~(Var U)))
                                              (RBind `{{x}} (Pi (RApp (Var el) (Var `{{code}})) `(Type))
                                                 (RApp (Var el) (RApp (Var `{{body}}) (Var `{{x}})))))),
                            MkFunClause (RApp (Var el) (Var `{{DataDef.Base}})) `(Bool)

                          ]

%runElab mkU

tt : el Base
tt = True

fun : el (Pi Base (\x => if x then Base else Pi Base (const Base)))
fun = \x => (case x of
               False => \y => False
               True => False)


nope : Elab ()
nope = defineDatatype $ DefineDatatype `{Either} [
           Constructor `{{Middle}} [ MkFunArg `{{x}} `(Type) Implicit NotErased
                                   , MkFunArg `{{y}} `(Type) Implicit NotErased
                                   ] `(Either ~(Var `{{x}}) ~(Var `{{y}}))
       ]
%runElab nope
 

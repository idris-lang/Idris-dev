module Pruviloj.Injective

import Language.Reflection.Utils

import Pruviloj.Core
import Pruviloj.Internals
import Pruviloj.Renamers

%default total
%access private

-------------------
-- PRIVATE GUTS  --
-------------------

||| Compute the name for a constructor's injectivity lemma
injName : TTName -> TTName
injName cn = NS (SN (MetaN `{{injectivity}} cn)) ["Injective", "Pruviloj"]

||| Provide an error message for when non-constructor names are passed
notConstructor : TTName -> Elab a
notConstructor c = fail [NamePart c, TextPart "is not a constructor"]

covering
getInjectivity : (cn : TTName) -> Elab TTName
getInjectivity cn = exists <|> declare
  where exists : Elab TTName
        exists = do (fn, Ref, _) <- lookupTyExact (injName cn)
                      | (fn, _, _) => fail [TextPart "Bad earlier declaration of", NamePart fn]
                    pure fn

        covering
        declare : Elab TTName
        declare = do (cn', DCon _ _, cty) <- lookupTyExact cn
                       | _ => notConstructor cn
                     let fn = injName cn'
                     (args1, res1) <- stealBindings !(forget cty) noRenames
                     (args2, res2) <- stealBindings !(forget cty) noRenames
                     let impls1 = map (\(n, b) => MkFunArg n (binderTy b) Implicit NotErased)
                                      args1
                     let impls2 = map (\(n, b) => MkFunArg n (binderTy b) Implicit NotErased)
                                      args2
                     let res = foldr (\t1, t2 => RApp (RApp (Var `{Pair}) t1) t2)
                                     `(() : Type)
                                     (map (\(a1, a2) =>
                                            `((=) {A=~(type a1)}
                                                  {B=~(type a2)}
                                                  ~(Var (name a1))
                                                  ~(Var (name a2))))
                                          (zip impls1 impls2))

                     declareType $ Declare fn (impls1 ++ impls2 ++
                                               [ MkFunArg !(gensym "arg")
                                                          `((=) {A=~res1}
                                                                {B=~res2}
                                                                ~(mkApp (Var cn)
                                                                        (map (Var . fst) args1))
                                                                ~(mkApp (Var cn)
                                                                        (map (Var . fst) args2)))
                                                          Explicit
                                                          NotErased])

                                           res
                     clause <- elabPatternClause
                                 (do (h::_) <- reverse <$>
                                                 apply (Var fn)
                                                       (replicate (2 * length args1)
                                                                  True ++
                                                        [False])
                                       | _ => fail [TextPart "Missing hole"]
                                     solve
                                     focus h; search)
                                 search -- rhs is conjunction of Refls
                     defineFunction $
                       DefineFun fn [clause]
                     pure fn

countBinders : TT -> Nat
countBinders (Bind _ _ body) = S (countBinders body)
countBinders _ = Z


----------------------
-- PUBLIC INTERFACE --
----------------------


||| Given an equality of the form `(C x1 ... xn = C y1 ... yn)`,
||| generate an product of the equalities `(x1 = y1)` ... `(xn = yn)`.
|||
||| The equalities are let-bound to the provided name.
|||
||| @ tm the equality to exploit injectivity on
||| @ n the name at which to bind the result
covering public export
injective : (tm : Raw) -> (n : TTName) -> Elab ()
injective tm n =
  do (_, ty) <- check !getEnv tm
     case !(forget ty) of
       `((=) {A=~A} {B=~B} ~x ~y) =>
         case (headName x, headName y) of
           (Just xHd, Just yHd) =>
             if xHd /= yHd
               then fail [ TextPart "Mismatch between", NamePart xHd
                         , TextPart "and", NamePart yHd
                         ]
               else do fn <- getInjectivity xHd
                       tyH <- newHole "ty" `(Type)
                       tmH <- newHole "tm" (Var tyH)

                       letbind n (Var tyH) (Var tmH)
                       focus tmH
                       (_, _, fnTy) <- lookupTyExact fn

                       (arg :: _) <- reverse <$> apply (Var fn) (replicate (pred (countBinders fnTy)) True ++ [False])
                         | _ => fail [TextPart "No hole for argument"]
                       solve

                       focus arg; apply tm []; solve
           _ => fail [TextPart "oops"]

       _ => fail [TextPart "can't use injectivity on non-equality"]

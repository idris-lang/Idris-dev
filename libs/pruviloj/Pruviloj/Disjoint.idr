||| Provides a tactic for solving constructor disjointness goals.
module Pruviloj.Disjoint

import Language.Reflection.Utils

import Pruviloj.Core
import Pruviloj.Internals
import Pruviloj.Renamers

%default total
%access private

-------------------
-- PRIVATE GUTS  --
-------------------

||| Compute the name to use for a disjointness lemma.
disjointName : TTName -> TTName -> TTName
disjointName l r = NS (SN (MetaN (UN "disjoint") (SN (MetaN l r))))
                      ["Disjoint", "Pruviloj"]

||| Compute the type to use for a disjointness lemma.
covering
disjointnessType : (l, r : TTName) -> Elab (TTName, List FunArg, Raw)
disjointnessType l r =
   do (l', DCon _ _, lty) <- lookupTyExact l
        | _ => notConstructor l
      (r', DCon _ _, rty) <- lookupTyExact r
        | _ => notConstructor r
      let fn = disjointName l' r'
      when (l' == r') $
        fail [ NamePart l', TextPart "and"
             , NamePart r', TextPart "are clearly not disjoint!"
             ]
      (argsl, resl) <- stealBindings !(forget lty) noRenames
      (argsr, resr) <- stealBindings !(forget rty) noRenames
      let args = map {b=FunArg}
                    (\(n, b) => MkFunArg n (binderTy b) Implicit NotErased)
                    (argsl ++ argsr)
      let eq : Raw = `((=) {A=~resl}
                          {B=~resr}
                          ~(mkApp (Var l') (map (Var . fst) argsl))
                          ~(mkApp (Var r') (map (Var . fst) argsr)))
      h <- gensym "h"
      pure (fn, args ++ [MkFunArg h eq Explicit NotErased], `(Void))
  where
    notConstructor : TTName -> Elab a
    notConstructor c = fail [NamePart c, TextPart "is not a constructor"]

||| Return the name of the disjointness lemma for two constructors,
||| defining it if necessary.
|||
||| @ l one of the constructor names
||| @ r the other constructor name
covering
getDisjointness : (l, r : TTName) -> Elab TTName
getDisjointness l r = exists <|> declare
  where exists : Elab TTName
        exists = do (yep, _, _) <- lookupTyExact (disjointName l r)
                    pure yep
        covering
        declare : Elab TTName
        declare = do (fn, args, ret) <- disjointnessType l r
                     declareType $ Declare fn args ret
                     defineFunction $ DefineFun fn []
                     pure fn

----------------------
-- PUBLIC INTERFACE --
----------------------


||| Solve a goal of the form `(C1 x1 x2 ... xn = C2 x1 x2 ... xn) ->
||| Void` for disjoint constructors `C1` and `C2`.
public export covering
disjoint : Elab ()
disjoint =
  do compute
     g <- snd <$> getGoal
     case g of
       `(((=) {A=~aTy} {B=~bTy} ~a ~b) -> Void) =>
         do Just lHead <- headName <$> forget a
              | Nothing => fail [TermPart a, TextPart "doesn't have a name at the head"]
            Just rHead <- headName <$> forget b
              | Nothing => fail [TermPart b, TextPart "doesn't have a name at the head"]
            [] <- refine (Var !(getDisjointness lHead rHead))
              | _ => fail [TextPart "Didn't solve argument to disjointness lemma"]
            skip
       ty =>
         fail [NamePart `{disjoint}, TextPart "is not applicable to goal", TermPart ty]

||| Solve a goal when there is an hypothesis of the form
||| `(C1 x1 x2 ... xn = C2 x1 x2 ... xn)`
||| for disjoint constructors `C1` and `C2`.
||| Similar to `discriminate` in Coq.
public export covering
discriminate : Elab ()
discriminate =
   do compute
      g <- goalType
      -- for each thing in the context, until we find one that succeeds
      flip choiceMap !getEnv $ \(n, b) =>
        do -- 1) check if it is an equality
           `(((=) {A=~aTy} {B=~bTy} ~a ~b)) <- forget (binderTy b)
             | _ => fail [TextPart "Not equality type"]
           -- 2) check if both sides of the equality have heads
           case (headName a, headName b) of
             (Just lHead, Just rHead) =>
               do lemma <- Var <$> getDisjointness lHead rHead
                  -- 3) learn how many arguments the lemma takes
                  (_, x :: xs, _) <- disjointnessType lHead rHead
                    | _ => fail [TextPart "Disjointness type takes no argument"]
                  -- 4) try to apply and focus on the last hole
                  apply `(void {a=~g}) [False]
                  solve
                  -- 5) try to call the disjointness lemma
                  -- We only want to pass the last arg explicitly to the lemma
                  let bools = map (const True) xs ++ [False]
                  (h :: hs) <- apply lemma bools
                    | _ => fail [TextPart "Disjointness lemma produces no holes"]
                  solve
                  -- 6) try to pass the current equality as an argument
                  focus (last (h :: hs))
                  exact (Var n)
             _ => fail [TextPart "Equality sides don't have a name at the head"]

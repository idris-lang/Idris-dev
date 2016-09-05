||| Derive implementations of decidable equality.
module Pruviloj.Derive.DecEq

import Data.Fin
import Data.Vect

import Language.Reflection.Utils

import Pruviloj.Core

import Pruviloj.Renamers
import Pruviloj.Internals

import Pruviloj.Derive.Eliminators

import Pruviloj.Disjoint
import Pruviloj.Induction
import Pruviloj.Injective

%default total
%access private


covering
noCase : TTName -> Elab ()
noCase contra =
  do [_, nope] <- apply (Var `{No}) [True, False]
       | _ => fail [TextPart "Bad holes from", NamePart `{Tactics.apply}]
     solve
     focus nope

     -- Construct a lambda binding an assumption from which we can
     -- derive the contradiction
     h <- gensym "h"
     inj <- gensym "inj"
     attack
     intro h
     injective (Var h) inj
     unproduct (Var inj)
     ignore $ refine (Var contra) `andThen` hypothesis
     solve -- attack

partial -- TODO make covering/total
matchCase : List Raw -> Elab ()
matchCase []          = search
matchCase (tm :: tms) =
    do (y :: n :: _)  <- induction tm

       focus n; compute
       contra <- gensym "contra"
       attack; intro contra
       noCase contra; solve

       focus y; compute
       prf <- gensym "prf"
       attack; intro prf
       rewriteWith (Var prf)
       matchCase tms
       solve

spanM : (Monad m) => (a -> m Bool) -> List a -> m (List a, List a)
spanM p [] = pure ([], [])
spanM p (x::xs) =
    if !(p x)
      then do (yes, no) <- spanM p xs
              pure (x :: yes, no)
      else pure ([], x::xs)

partitionM : Monad m => (a -> m Bool) -> List a -> m (List a, List a)
partitionM p [] = pure ([], [])
partitionM p (x :: xs) =
    do (y, n) <- partitionM p xs
       if !(p x) then pure (x :: y, n) else pure (y, x :: n)

perhaps : (Alternative f) => (f a) -> (f (Maybe a))
perhaps x = (Just <$> x) <|> pure Nothing

headIs : Raw -> TTName -> Bool
headIs tm n = maybe False (==n) (headName tm)

partial
mkRhs : (fn, fam : TTName) -> Nat -> Elab ()
mkRhs fn fam k =
    case snd !getGoal of
      `(Dec ((=) {A=~A} {B=~_} ~x ~y)) =>
        let (c1, args1) = unApply x
            (c2, args2) = unApply y
        in if c1 /= c2
             then do (h :: _) <- refine (Var `{No})
                       | _ => empty
                     focus h
                     disjoint
             else do let toMakeEqual = List.filter (uncurry (/=)) (zip args1 args2)
                     tms <- for {b=Raw} toMakeEqual $ \(tm1, tm2) =>
                       do env <- getEnv
                          (tm1', ty1') <- forget tm1 >>= check env
                          (tm2', ty2') <- forget tm2 >>= check env
                          -- assume they have the same type here -
                          -- reasonable due to same constructor, but
                          -- this means order is important when
                          -- traversing
                          eq <- gensym "eq"
                          rTy <- forget ty1'
                          rTm1 <- forget tm1'
                          rTm2 <- forget tm2'
                          remember eq `(Dec ((=) {A=~rTy} {B=~rTy} ~rTm1 ~rTm2))
                          simple $
                            if headIs rTy fam
                              then do (a2::a1::hs) <- reverse <$> apply (Var fn) (replicate k True ++ [False, False])
                                      solve
                                      focus a1; fill rTm1; solve
                                      focus a2; fill rTm2; solve
                                      for_ hs $ \h => inHole h (resolveTC fn)
                              else do [_, dH, a1, a2] <- apply (Var `{decEq}) [True, False, False, False]
                                      solve
                                      focus a1; fill rTm1; solve
                                      focus a2; fill rTm2; solve
                                      focus dH; resolveTC fn
                          pure (Var eq)
                     matchCase tms
      _ => fail [TextPart "Inapplicable"]

||| Attempt to derive the body of an implementation of decidable
||| equality based on an existing type signature.
|||
||| The function signature must provide enough information for the
||| deriving to occur. It must consist of zero or more non-constraint
||| arguments followed by zero or more constraint arguments, followed
||| by the two values to compare. The constraint arguments must
||| provide sufficient implementations of `DecEq` to decide the equality of
||| each constructor field. The final two arguments to the function
||| declaration must be the two values that will be compared for
||| equality.
|||
||| @ fn the name of the function whose type has been declared
export partial -- because of mkRhs
deriveDecEq : (fn : TTName) -> Elab ()
deriveDecEq fn =
    do (_, Ref, sig') <- lookupTyExact fn
       sig <- forget sig'
       (args, `(Dec ((=) {A=~A} {B=~_} ~(Var x) ~(Var y)))) <- stealBindings sig noRenames
         | other => fail [ TextPart "Return type"
                         , RawPart (snd other)
                         , TextPart "isn't decidable equality"
                         ]

       datatype <- maybe (fail [ RawPart A
                               , TextPart "is not an application of a TC"
                               ])
                         lookupDatatypeExact
                         (headName A)

       -- the signature must be like this:
       -- 1. a collection of variable bindings (will be implicit)
       -- 2. a collection of constraints
       -- 3. the arguments x and y from the return type
       (bindings, constrs, arg1, arg2) <-
         the (Elab (List (TTName, Binder Raw),
                    List (TTName, Binder Raw),
                    (TTName, Binder Raw),
                    (TTName, Binder Raw))) $
           case reverse args of
             [] => fail [TextPart "Invalid signature"]
             [_] => fail [TextPart "Invalid signaure"]
             (a2 :: a1 :: rest) =>
               do (constrs, bindings) <- partitionM (\x => isConstr (binderTy (snd x)))
                                                    (reverse rest)
                  pure (bindings, constrs, a1, a2)
       let todo = [(c1, c2) | c1 <- constructors datatype
                            , c2 <- constructors datatype]
       clauses <- for todo
                      (uncurry $ mkCase (length bindings + length constrs)
                                        (name datatype))
       defineFunction $ DefineFun fn (catMaybes clauses)
       skip

  where
    isConstr : Raw -> Elab Bool
    isConstr tm = case headName tm of
                    Just n => isTCName n
                    Nothing => pure False

    partial -- mkRhs
    mkCase : Nat -> TTName -> (x, y : (TTName, List CtorArg, Raw)) -> Elab (Maybe (FunClause Raw))
    mkCase k fam (cn1, args1, _) (cn2, args2, _) =
        perhaps $ elabPatternClause
          (do (h2 :: h1 :: _) <- reverse <$>
                                   apply (Var fn) (replicate k True ++ [False, False])
              solve
              focus h1
              apply (Var cn1) (replicate (length args1) True)
              solve
              focus h2
              apply (Var cn2) (replicate (length args2) True)
              solve)
          (mkRhs fn fam k)

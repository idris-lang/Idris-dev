||| Core tactics for working with Elab reflection. These will be used
||| by most reasonable scripts, and they may be candidates for
||| eventual Prelude inclusion.
module Pruviloj.Core

import Language.Reflection.Utils

%access public export

||| Do nothing
skip : Applicative f => f ()
skip = pure ()

||| Attempt to apply a tactic. If it fails, do nothing.
try : Alternative f => f a -> f ()
try tac = ignore tac <|> pure ()

||| Remove type information from a `TT` term, in a context. Fails if
||| de Bruijn indices are out of scope.
forget' : List TTName -> TT -> Elab Raw
forget' env (P nt n tm) = pure (Var n)
forget' env (V x) = Var <$> getName x env
  where getName : Int -> List a -> Elab a
        getName _ [] = fail [TextPart "Scope error when forget'ting types"]
        getName i (n::ns) = if i <= 0 then pure n else getName (i-1) ns
forget' env (Bind n b tm) =
    [| (RBind n)
       (assert_total $ traverse (forget' env) b)
       (forget' (n::env) tm) |]
forget' env (App tm tm') = [| RApp (forget' env tm) (forget' env tm') |]
forget' env (TConst c) = pure (RConstant c)
forget' env Erased = pure (RConstant Forgot)
forget' env (TType uexp) = pure RType
forget' env (UType uni) = pure (RUType uni)

||| Remove type information from a `TT` term. Fails if de Bruijn
||| indices are out of scope.
forget : TT -> Elab Raw
forget tm = forget' [] tm

||| Get the goal type as a Raw term. Fails if there are no holes.
goalType : Elab Raw
goalType = do g <- getGoal
              forget (snd g)

||| Solve the goal using the most recent applicable hypothesis
hypothesis : Elab ()
hypothesis =
    do hyps <- map fst <$> getEnv
       flip choiceMap hyps $ \n =>
         do fill (Var n)
            solve


||| Generate a unique name (using `gensym`) that looks like some
||| previous name, for ease of debugging code generators.
nameFrom : TTName -> Elab TTName
nameFrom (UN x) =
    gensym $ if length x == 0 || ("_" `isPrefixOf` x)
               then "x"
               else x
nameFrom (NS n ns) =
    nameFrom n -- throw out namespaces here, because we want to
               -- generate bound var names
nameFrom (MN x n) =
    gensym $ if length n == 0 || ("_" `isPrefixOf` n)
               then "n"
               else n
nameFrom (SN x) = gensym "SN"

||| Get the name at the head of the term, if it exists.
headName : Raw -> Maybe TTName
headName (RApp f _) = headName f
headName (Var n) = Just n
headName x = Nothing

||| Create a new hole with a given type without changing the
||| focus. Return the name of the hole.
|||
||| @ hint the hint to pass to `gensym`
||| @ ty the type of the new hole
newHole : (hint : String) -> (ty : Raw) -> Elab TTName
newHole hint ty =
    do hn <- gensym hint
       claim hn ty
       pure hn

||| Use a term to solve a hole
|||
||| @ tm the term that has the right type for the hole
exact : (tm : Raw) -> Elab ()
exact tm = do fill tm
              solve

||| Introduce as many names as possible, returning them.
intros : Elab (List TTName)
intros = do g <- snd <$> getGoal
            go g
  where go : TT -> Elab (List TTName)
        go (Bind n (Pi _ _) body) =
            do n' <- nameFrom n
               intro n'
               (n' ::) <$> go body
        go _ = pure []

||| Run a tactic inside of a particular hole, if it still exists. If
||| it has been solved, do nothing.
inHole : TTName -> Elab a -> Elab (Maybe a)
inHole h todo =
  if (h `elem` !getHoles)
    then do focus h; Just <$> todo
    else pure Nothing

||| Restrict a polymorphic type to () for contexts where it doesn't
||| matter. This is nice for sticking `debug` in a context where
||| Idris can't solve the type.
simple : {m : Type -> Type} -> m () -> m ()
simple x = x

||| Replace the current goal with one that's definitionally
||| equal. Return the name of the new goal, and ensure that it's
||| focused.
|||
||| @ newGoal A type that is equivalent to the current goal
equiv : (newGoal : Raw) -> Elab TTName
equiv newGoal =
    do h <- gensym "goal"
       claim h newGoal
       fill (Var h); solve
       focus h
       pure h

||| Remember a term built with elaboration for later use. If the
||| current goal is `h`, then `remember n ty` puts a fresh hole at
||| the front of the queue, with the old goal `h` second. The
||| contents of this hole end up let-bound in the scope of
||| `h`. Return the name of the new hole, in case it will be used
||| later.
|||
||| @ n the name to be used to save the term
||| @ ty the type to inhabit
remember : (n : TTName) -> (ty : Raw) -> Elab TTName
remember n ty =
    do todo <- gensym "rememberThis"
       claim todo ty
       letbind n ty (Var todo)
       focus todo
       pure todo

||| Repeat a given tactic until it fails. Fails if the tactic fails on
||| the first attempt; succeeds otherwise.
repeatUntilFail : Elab () -> Elab ()
repeatUntilFail tac =
    do tac
       repeatUntilFail tac <|> pure ()

||| If the current goal is a pattern-bound variable, bind it with the
||| expected name. Otherwise fail.
bindPat : Elab ()
bindPat = do compute
             g <- snd <$> getGoal
             case g of
               Bind n (PVTy _) _ => patbind n
               _ => fail [TermPart g, TextPart "isn't looking for a pattern."]

||| The underlying implementation type for the inferType operator.
data Infer : Type where
  MkInfer : (a : Type) -> a -> Infer

||| Run a tactic script in a context where the type of the resulting
||| expression must be solvable via unification. Return the term and
||| its type.
|||
||| @ tac a tactic script that will be run with focus on the hole
|||       whose type is to be inferred.
total
inferType : (tac : Elab ()) -> Elab (TT, TT)
inferType tac =
    case fst !(runElab `(Infer) (do startInfer; tac)) of
        `(MkInfer ~ty ~tm) => pure (tm, ty)
        _ => fail [TextPart "Not infer"]
  where
    startInfer : Elab ()
    startInfer = do [_, tmH] <- apply (Var `{MkInfer}) [True, False]
                       | err => fail [TextPart "Type inference failure"]
                    solve
                    focus tmH

||| Given one tactic that produces a list of subgoal names and another
||| that produces some result, run the second tactic in each hole
||| produced by the first and return the resulting values.
|||
||| Elab has no built-in notion of "subgoals", so this simulates the
||| Coq or JonPRL semicolon operators.
|||
||| @ first run this tactic to produce subgoals
||| @ after run this tactic in each subgoal
andThen : (first : Elab (List TTName)) -> (after : Elab a) -> Elab (List a)
andThen first after =
    do hs <- first
       catMaybes <$> for hs (flip inHole after)

||| Refine the current goal using some term, constructing holes for
||| all arguments that can't be inferred. Return the list of generated
||| holes.
|||
||| @ tm the term to apply to some number of goals
refine : (tm : Raw) -> Elab (List TTName)
refine tm =
    do ty <- (snd <$> check !getEnv tm) >>= forget
       g <- goalType

       -- we don't care about negative results because it'll just fail anyway
       let argCount = minus (countPi ty) (countPi g)
       newHoles <- apply tm (replicate argCount True)
       solve
       actualHoles <- getHoles
       pure (filter (flip elem actualHoles) newHoles)

  where countPi : Raw -> Nat
        countPi (RBind _ (Pi _ _) body) = S (countPi body)
        countPi _ = Z

||| A helper to extract the type representation for term.
getTTType : Raw -> Elab TT
getTTType r = snd <$> check !getEnv r

||| Split a pair into its projections, binding them in the context
||| with the supplied names. A special case of Coq's `inversion`.
both : Raw -> TTName -> TTName -> Elab ()
both tm n1 n2 =
    do -- We don't know that the term is canonical, so let-bind projections applied to it
       (a, b) <- isPairTy !(getTTType tm)
       remember n1 a; apply `(fst {a=~a} {b=~b} ~tm) []; solve
       remember n2 b; apply `(snd {a=~a} {b=~b} ~tm) []; solve
  where
    isPairTy : TT -> Elab (Raw, Raw)
    isPairTy `((~a, ~b) : Type) = [| MkPair (forget a) (forget b) |]
    isPairTy tm = fail [TermPart tm, TextPart "is not a pair"]

||| Let-bind all results of completely destructuring nested tuples.
|||
||| This makes them available to the `hypothesis` tactic, among others.
|||
||| @ tm the nested tuple to destructure
covering
unproduct : (tm : Raw) -> Elab ()
unproduct tm =
    do n1 <- gensym "left"
       n2 <- gensym "right"
       both tm n1 n2
       try (unproduct (Var n1))
       try (unproduct (Var n2))

||| Try to apply the constructors of the goal data type one by one,
||| and apply the first one that works. If one of the constructors work,
||| the explicit arguments to the constructor are created as new holes and
||| the hole names are returned in a list. The parameters of the type and
||| the implicit arguments of the constructor will be solved by unification.
||| Similar to `constructor` in Coq.
construct : Elab (List TTName)
construct = case headName !goalType of
    Nothing =>
      fail [TextPart "Goal is not of a type declared with the data keyword"]
    Just h =>
      choiceMap (\(n, xs, _) => apply (Var n) (map shouldUnify xs) <* solve)
                !(constructors <$> lookupDatatypeExact h)
      <|> fail [TextPart "No constructors apply"]
  where
    shouldUnify : CtorArg -> Bool
    shouldUnify (CtorField (MkFunArg _ _ Explicit _)) = False
    shouldUnify _ = True

||| A special-purpose tactic that attempts to solve a goal using
||| `Refl`. This is useful for ensuring that goals in fact are trivial
||| when developing or testing other tactics; otherwise, consider
||| using `search`.
reflexivity : Elab ()
reflexivity =
    case !goalType of
      `((=) {A=~a} {B=~_} ~x ~_) =>
        do fill `(Refl {A=~a} {x=~x})
           solve
      _ => fail [ TextPart "The goal is not an equality, so"
                , NamePart `{reflexivity}
                , TextPart "is not applicable."
                ]

||| Attempt to swap the sides of equality in a goal. If the goal is `x = y`,
||| after the invocation the focus will be on a hole of type `y = x`.
symmetry : Elab ()
symmetry =
    do [_,_,_,_,res] <- apply (Var `{{sym}}) [True, True, True, True, False]
          | _ => fail [TextPart "Failed while applying", NamePart `{symmetry}]
       solve
       focus res

||| Swap the sides of an equality, saving the result in a `let`-binding.
||| Returns the generated name.
|||
||| @ t the equality proof to swap
||| @ hint a hint to use for generating the variable name for the result
symmetryAs : (t : Raw) -> (hint : String) -> Elab TTName
symmetryAs t hint =
    case !(getTTType t) of
      `((=) {A=~a} {B=~b} ~l ~r) =>
        do af <- forget a
           bf <- forget b
           lf <- forget l
           rf <- forget r
           let ts = the Raw $ `(sym {a=~af} {b=~bf} {left=~lf} {right=~rf} ~t)
           n <- gensym hint
           letbind n !(forget !(getTTType ts)) ts
           pure n
      tt => fail [TermPart tt, TextPart "is not an equality"]

||| Apply a function term to an argument term, saving the result in a
||| `let`-binding. Returns the generated name.
|||
||| @ f the function to apply
||| @ x the term to apply to
||| @ hint a hint to use for generating the variable name for the result
applyAs : (f : Raw) -> (x : Raw) -> (hint : String) -> Elab TTName
applyAs f x hint =
    case !(getTTType f) of
      `(~xty -> ~yty) =>
         do let fx = RApp f x
            n <- gensym hint
            letbind n !(forget !(getTTType fx)) fx
            pure n
      ftt => fail [TermPart ftt, TextPart "is not a function"]

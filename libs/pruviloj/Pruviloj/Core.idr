||| Core tactics for working with Elab reflection. These will be used
||| by most reasonable scripts, and they may be candidates for
||| eventual Prelude inclusion.
module Pruviloj.Core

import Language.Reflection.Utils

||| Run something for effects, throwing away the return value
ignore : Functor f => f a -> f ()
ignore x = map (const ()) x

||| Do nothing
skip : Applicative f => f ()
skip = pure ()

||| Attempt to apply a tactic. If it fails, do nothing.
try : Alternative f => f a -> f ()
try tac = ignore tac <|> pure ()

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
nameFrom NErased = gensym "wasErased"

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
       return hn

||| Use a term to solve a hole
|||
||| @ tm the term that has the right type for the hole
exact : (tm : Raw) -> Elab ()
exact tm = do apply tm []
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
        go _ = return []

||| Run a tactic inside of a particular hole, if it still exists. If
||| it has been solved, do nothing.
inHole : TTName -> Elab a -> Elab (Maybe a)
inHole h todo =
  if (h `elem` !getHoles)
    then do focus h; Just <$> todo
    else return Nothing

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
       return h

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
       return todo

||| Repeat a given tactic until it fails. Fails if the tactic fails on
||| the first attempt; succeeds otherwise.
repeatUntilFail : Elab () -> Elab ()
repeatUntilFail tac =
    do tac
       repeatUntilFail tac <|> return ()

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
    case fst !(runElab `(Infer) (startInfer *> tac)) of
        `(MkInfer ~ty ~tm) => return (tm, ty)
        _ => fail [TextPart "Not infer"]
  where
    startInfer : Elab ()
    startInfer = do [_, (_, tmH)] <- apply (Var `{MkInfer}) [(True, 0), (False, 1)]
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
    do ty <- (snd <$> check tm) >>= forgetTypes
       g <- goalType

       -- we don't care about negative results because it'll just fail anyway
       let argCount = minus (countPi ty) (countPi g)
       newHoles <- apply tm (replicate argCount (True, 0))
       solve
       actualHoles <- getHoles
       return (filter (flip elem actualHoles) (map snd newHoles))

  where countPi : Raw -> Nat
        countPi (RBind _ (Pi _ _) body) = S (countPi body)
        countPi _ = Z

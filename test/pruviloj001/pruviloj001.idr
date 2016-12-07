-- Demonstrate that partial tactics can produce total programs and
-- that the basic parts of Pruviloj are doing what they should.

import Pruviloj
import Pruviloj.Induction

%default total
%language ElabReflection

||| Try some simplification and rewriting heuristics, then attempt to
||| solve the goal
partial
auto : Elab ()
auto = do compute
          attack
          try intros
          hs <- map fst <$> getEnv
          for_ hs $
            \ih => try (rewriteWith (Var ih))
          hypothesis <|> search
          solve

||| Common pattern of proofs by induction.
partial
mush : Elab ()
mush =
    do attack
       n <- gensym "j"
       intro n
       try intros
       ignore $ induction (Var n) `andThen` auto
       solve

plusAssoc : (j, k, l : Nat) -> plus (plus j k) l = plus j (plus k l)
plusAssoc = %runElab mush

plusZeroR : (k : Nat) -> plus k Z = k
plusZeroR = %runElab mush

plusSRightS : (left : Nat) -> (right : Nat) -> S (left + right) = left + (S right)
plusSRightS = %runElab mush

multOneLNeutral : (right : Nat) -> 1 * right = right
multOneLNeutral = %runElab mush

multOneRNeutral : (left : Nat) -> left * 1 = left
multOneRNeutral = %runElab mush

plusMinusLeftCancel : (left : Nat) -> (right : Nat) -> (right' : Nat) ->
                      minus (left + right) (left + right') = minus right right'
plusMinusLeftCancel = %runElab mush

powerOneNeutral : (base : Nat) -> power base 1 = base
powerOneNeutral = %runElab mush

-- this silly tactic is controllable by introducing the non-inductive arg first
mapPreservesLen : (f : a -> b) -> (l : List a) ->
                  length (map f l) = length l
mapPreservesLen f = %runElab mush

lenAppend : (left : List a) -> (right : List a) ->
            length (left ++ right) = length left + length right
lenAppend = %runElab mush

appendNilRightId : (l : List a) ->
                   l ++ [] = l
appendNilRightId = %runElab mush

-- Local Variables:
-- idris-load-packages: ("pruviloj")
-- End:

||| A work-in-progress demonstration of Idris elaborator metaprogramming.
||| Goals:
|||  * Let tactics query the environment, for things like type signatures
|||  * Tactics expressions should be normal Idris expressions, and support
|||    things like idiom brackets, Alternative, etc
|||  * Make user-defined tactics just as easy to use as built-in ones
module Tacs

import Data.Fin
import Data.Vect

import Language.Reflection
import Language.Reflection.Errors
import Language.Reflection.Utils

import Pruviloj.Core

%default total
%language ElabReflection

-- Tactics can now query the elaborator and bind variables

--stuff : Nat -> Nat -> Nat
--stuff x y = %runElab (debugMessage "oh noes")

intros : Elab ()
intros = do g <- getGoal
            case snd g of
              `(~_ -> ~_) => intro'
              _ => pure ()

foo : Nat -> Nat
foo = %runElab (do intro (UN "fnord")
                   fill `(plus ~(Var (UN "fnord")) ~(Var (UN "fnord")))
                   solve)


%runElab (do n <- isTCName `{Nat}
             s <- isTCName `{Show}
             if n || not s then fail [TextPart "nope"] else pure ())

-- Note that <|> is equivalent to "try" in the old tactics.
-- In these tactics, we use ordinary do notation and ordinary documentation strings!
||| Try to solve a goal with simple guesses of easy type
triv : Elab ()
triv = do fill `(Z) <|> fill `(() : ())
          solve


-- Solve both kinds of goal. The %runElab construction elaborates
-- to the result of running the tactic script that it contains.

test1 : ()
test1 = %runElab triv

test2 : Nat
test2 = %runElab triv

partial
obvious : Elab ()
obvious = do g <- goalType
             case g of
               `(() : Type) =>
                 do fill `(() : ())
                    solve
               `((~a, ~b) : Type) =>
                 do aH <- gensym "a"
                    bH <- gensym "b"
                    claim aH a
                    claim bH b
                    fill `(MkPair {A=~a} {B=~b} ~(Var aH) ~(Var bH))
                    solve
                    focus aH; obvious
                    focus bH; obvious
               `(Either ~a ~b) =>
                 (do h <- gensym "a"
                     claim h a
                     fill  `(Left {a=~a} {b=~b} ~(Var h))
                     solve
                     focus h; obvious) <|>
                   -- This second h didn't work at one point - this
                   -- test makes sure the fix stays fixed. The
                   -- uniquification of binder names didn't
                   -- appropriately treat quotation.
                   (do h <- gensym "a"
                       claim h b
                       fill `(Right {a=~a} {b=~b} ~(Var h))
                       solve
                       focus h; obvious)

easy : ()
easy = %runElab obvious


easy2 : ((), ((), (Either () Void)))
easy2 = %runElab obvious



namespace STLC

  data Ty = UNIT | ARR Ty Ty

  %name Ty t,t',t''

  implementation Quotable Ty TT where
    quotedTy = `(Ty : Type)
    quote UNIT = `(UNIT : Ty)
    quote (ARR t t') = `(ARR ~(quote t) ~(quote t'))

  elabTy : Ty -> Elab ()
  elabTy UNIT = do fill `(() : Type)
                   solve
  elabTy (ARR t t') = do arg <- gensym "__stlc_arg"
                         n1 <- mkTypeHole "t1"
                         n2 <- mkTypeHole "t2"
                         fill (RBind arg (Pi (Var n1) RType) (Var n2))
                         focus n1; elabTy t
                         focus n2; elabTy t'
                         solve
    where mkTypeHole : String -> Elab TTName
          mkTypeHole hint = do holeName <- gensym hint
                               claim holeName RType
                               unfocus holeName
                               pure holeName

  -- FIXME: Removing the let-bound Elab script showed a deficiency in
  -- how accessible arguments are identified in type signatures. It
  -- would be nice if this worked without the extraneous
  -- `let`. (perhaps a flag on Pi that says it came from the parser?)
  someDef : let x = () in %runElab ((elabTy $ ARR (ARR UNIT UNIT) (ARR UNIT UNIT)))
  someDef = id

  namespace Untyped
    ||| Completely untyped terms
    data UTm = Lam String UTm | App UTm UTm | Var String | UnitCon
    %name UTm tm,tm',tm''

  namespace Scoped
    ||| Scope-checked terms - we'll use tactics to infer their types!
    data STm : Nat -> Type where
      Lam : String -> STm (S n) -> STm n
      App : STm n -> STm n -> STm n
      Var : Fin n -> STm n
      UnitCon : STm n
    %name STm tm,tm',tm''

    ||| Find the de Bruijn index for a variable in a naming context
    findVar : Eq a => a -> Vect n a -> Maybe (Fin n)
    findVar x [] = Nothing
    findVar x (y :: xs) = if x == y then pure FZ else [| FS (findVar x xs) |]

    ||| Resolve the names in a term to de Bruijn indices
    scopeCheck : Vect n String -> UTm -> Either String (STm n)
    scopeCheck vars (Lam x tm) = [| (Lam x) (scopeCheck (x::vars) tm) |]
    scopeCheck vars (App tm tm') = [| App (scopeCheck vars tm)
                                          (scopeCheck vars tm') |]
    scopeCheck vars (Var x) = case findVar x vars of
                                Nothing => Left $ "Unknown var " ++ x
                                Just i => pure $ Var i
    scopeCheck vars UnitCon = pure UnitCon

    forgetScope : Vect n String -> STm n -> UTm
    forgetScope vars (Lam x tm) = Lam x (forgetScope (x::vars) tm)
    forgetScope vars (App tm tm') = App (forgetScope vars tm)
                                        (forgetScope vars tm')
    forgetScope vars (Var i) = Var $ index i vars
    forgetScope vars UnitCon = UnitCon

  namespace Typed

    Env : Type
    Env = List Ty
    %name Typed.Env env

    ||| Well-typed de Bruijn indices
    data Ix : Env -> Ty -> Type where
      Z : Ix (t::env) t
      S : Ix env t -> Ix (t'::env) t
    %name Ix i,j,k

    data Tm : List Ty -> Ty -> Type where
      Lam : {env : List Ty} -> {t, t' : Ty} ->
            Tm (t::env) t' -> Tm env (ARR t t')
      App : Tm env (ARR t t') -> Tm env t -> Tm env t'
      Var : Ix env t -> Tm env t
      UnitCon : Tm env UNIT

  namespace Inference
    inNS : String -> TTName
    inNS n = NS (UN n) ["STLC", "Tacs"]

    inTypedNS : String -> TTName
    inTypedNS n = NS (UN n) ["Typed", "STLC", "Tacs"]

    elaborateSTLC : STm 0 -> Elab ()
    elaborateSTLC tm =
      do -- We're going to fill out a goal that wants a Sigma Ty (Tm [])
         -- First establish a hole for the type (inferred by side effect,
         -- similar to Idris implicit args)
         tH <- gensym "t"
         claim tH (Var (inNS "Ty"))
         unfocus tH
         -- Next we make a hole that wants a term in that type
         tmH <- gensym "tm"
         let p : Raw = `(Tm [])
         claim tmH (RApp p (Var tH))
         unfocus tmH

         -- Now we put this hole variable into our sigma constructor
         -- prior to elaboration, so it doesn't disappear too soon
         fill `(MkDPair ~(Var tH) ~(Var tmH) : DPair Ty (Tm []))
         solve
         focus tmH
         mkTerm [] tm

        where mkEnvH : Elab TTName
              mkEnvH = do envH <- gensym "env"
                          claim envH `(List Ty)
                          unfocus envH
                          pure envH

              mkTyH : Elab TTName
              mkTyH = do tyH <- gensym "ty"
                         claim tyH `(Ty)
                         unfocus tyH
                         pure tyH

              mkIx : Fin n -> Elab ()
              mkIx FZ = do envH <- mkEnvH
                           tH <- mkTyH
                           apply `(Z {t=~(Var tH)} {env=~(Var envH)}) []
                           solve
              mkIx (FS i) = do envH <- mkEnvH
                               tH <- mkTyH
                               vH <- mkTyH
                               argH <- gensym "arg"
                               claim argH `(Ix ~(Var envH) ~(Var tH))
                               unfocus argH
                               apply `(S {env=~(Var envH)} {t=~(Var tH)} {t'=~(Var vH)} ~(Var argH)) []
                               solve
                               focus argH
                               mkIx i

              mkTerm : Vect n TTName -> STm n -> Elab ()
              mkTerm xs (Lam x tm) = do tH <- mkTyH
                                        envH <- mkEnvH
                                        tH' <- mkTyH
                                        bodyH <- gensym "body"
                                        claim bodyH `(Tm ((::) ~(Var tH) ~(Var envH)) ~(Var tH'))
                                        apply `(Lam {env=~(Var envH)}
                                                    {t=~(Var tH)} {t'=~(Var tH')}
                                                    ~(Var bodyH))
                                              []

                                        solve
                                        focus bodyH
                                        mkTerm (tH::xs) tm
              mkTerm xs (App tm tm') = do envH <- mkEnvH
                                          tH <- mkTyH
                                          tH' <- mkTyH
                                          fH <- gensym "f"
                                          claim fH `(Tm ~(Var envH) (ARR ~(Var tH) ~(Var tH')))
                                          unfocus fH
                                          argH <- gensym "arg"
                                          claim argH `(Tm ~(Var envH) ~(Var tH))
                                          unfocus argH
                                          apply `(App {env=~(Var envH)}
                                                      {t=~(Var tH)} {t'=~(Var tH')}
                                                      ~(Var fH) ~(Var argH))
                                                []
                                          solve
                                          focus fH
                                          mkTerm xs tm
                                          focus argH
                                          mkTerm xs tm'
              mkTerm xs (Var i) = do tH <- mkTyH
                                     envH <- mkEnvH
                                     ixH <- gensym "ix"
                                     claim ixH `(Ix ~(Var envH) ~(Var tH))
                                     unfocus ixH
                                     apply `(Var {env=~(Var envH)} {t=~(Var tH)} ~(Var ixH))
                                           []
                                     solve
                                     focus ixH
                                     mkIx i
              mkTerm xs UnitCon = do envH <- mkEnvH
                                     apply `(UnitCon {env=~(Var envH)})
                                           []
                                     solve
    testElab : DPair Ty (Tm [])
    testElab = %runElab (elaborateSTLC (App (Lam "x" UnitCon) UnitCon))

    testElab2 : DPair Ty (Tm [])
    testElab2 = %runElab (elaborateSTLC (App (Lam "x" (Var 0)) UnitCon))

    -- Doesn't work! :-)
    testElab3 : DPair Ty (Tm [])
    testElab3 = %runElab (elaborateSTLC (App (Lam "x" (App (Var 0) (Var 0)))
                                             (Lam "x" (App (Var 0) (Var 0)))))
    -- Error is:
    -- Tacs.idr line 247 col 14:
    --     When elaborating right hand side of testElab3:
    --     Unifying ty and Tacs.STLC.ARR ty t would lead to infinite value

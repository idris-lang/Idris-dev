module SourceLoc

import Data.Vect
import Data.Fin
import Language.Reflection
import Language.Reflection.Utils

%default total
%language DSLNotation

||| A "function" that returns where it is called in the source
getLoc : {default tactics { sourceLocation } x : SourceLocation} -> SourceLocation
getLoc {x} = x

||| A test of getLoc
fromRHS : SourceLocation
fromRHS = getLoc

||| Testing getting source locations from RHS proof scripts
fromProofScript : SourceLocation
fromProofScript = proof sourceLocation

||| Testing getting source locations from deferred proofs.
fromMetavar : SourceLocation
fromMetavar = ?meta

--- Testing that getting source locations in ASTs constructed with DSL notation
data Ty = U | Arr Ty Ty

interp : Ty -> Type
interp U         = ()
interp (Arr x y) = interp x -> Either SourceLocation (interp y)

using (ctxt : Vect n Ty)
  data Tm : Vect n Ty -> Ty -> Type where
    MkU : Tm ctxt U
    Var : (i : Fin n) -> Tm ctxt (index i ctxt)
    Lam : Tm (t::ctxt) t' -> Tm ctxt (Arr t t')
    App : Tm ctxt (Arr t t') -> Tm ctxt t -> Tm ctxt t'
    ||| A term that makes the program halt and printLn where it halted
    Die : {default tactics { sourceLocation } loc : SourceLocation} -> Tm ctxt t

  data Env : Vect n Ty -> Type where
    Nil : Env []
    (::) : interp t -> Env ctxt -> Env (t::ctxt)

  index : (i : Fin n) -> Env ctxt -> interp (index i ctxt)
  index FZ     (x::env) = x
  index (FS i) (x::env) = index i env

  run : Tm ctxt t -> Env ctxt -> Either SourceLocation (interp t)
  run MkU         _   = pure ()
  run (Var i)     env = pure $ index i env
  run (Lam bdy)   env = pure $ \x => run bdy (x::env)
  run (App f x)   env = !(run f env) !(run x env)
  run (Die {loc}) _   = Left loc

  lam_ : _ -> Tm (t::ctxt) t' -> Tm ctxt (Arr t t')
  lam_ _ = Lam

exec : Tm [] t -> IO ()
exec tm = case run tm [] of
            Left loc  => putStrLn $ "Error at " ++ show loc
            Right _   => putStrLn $ "Success!"

dsl lang
  variable = Var
  index_first = FZ
  index_next = FS
  lambda = lam_

testTerm1 : Tm [] (Arr U U)
testTerm1 = lang (\x=>Die)

testTerm2 : Tm [] U
testTerm2 = App testTerm1 MkU

testTerm3 : Tm [] (Arr U U)
testTerm3 = lang (\x => MkU)

testTerm4 : Tm [] U
testTerm4 = App testTerm3 MkU

namespace Main
  main : IO ()
  main = do putStrLn "Testing using definition"
            printLn fromRHS
            putStrLn "Testing using inline tactics"
            printLn fromProofScript
            putStrLn "Testing using metavariable with later definition"
            printLn fromMetavar
            putStrLn "-----------------------"
            sequence_ $ with List [ exec testTerm1
                                  , exec testTerm2
                                  , exec testTerm3
                                  , exec testTerm4
                                  ]
---------- Proofs ----------
SourceLoc.meta = proof
  sourceLocation




module Finite

import Data.Fin
import Language.Reflection.Elab
import Language.Reflection.Utils

%language ElabReflection

-- Test various features of reflected elaboration, including looking
-- up datatypes, defining functions, and totality checking

%default total

||| A bijection between some type and bounded numbers
data Finite : Type -> Nat -> Type where
  IsFinite : (toFin : a -> Fin n) ->
             (fromFin : Fin n -> a) ->
             (ok1 : (x : a) -> fromFin (toFin x) = x) ->
             (ok2 : (y : Fin n) -> toFin (fromFin y) = y) ->
             Finite a n

acceptableConstructor : Raw -> Bool
acceptableConstructor (Var _) = True
acceptableConstructor _ = False

mkFin : Nat -> Nat -> Elab Raw
mkFin Z j = fail [TermPart `(Fin Z), TextPart "is uninhabitable!"]
mkFin (S k) Z = pure `(FZ {k=~(quote k)})
mkFin (S k) (S j) = do i <- mkFin k j
                       pure `(FS {k=~(quote k)} ~i)

mkToClause : TTName -> (size, i : Nat) ->
             (constr : (TTName, List CtorArg, Raw)) ->
             Elab (FunClause Raw)
mkToClause fn size i (n, [], Var ty) =
  MkFunClause (RApp (Var fn) (Var n)) <$> mkFin size i
mkToClause fn size i (n, _, ty) =
  fail [TextPart "unsupported constructor", NamePart n]


mkFromClause : TTName -> (size, i : Nat) ->
               (constr : (TTName, List CtorArg, Raw)) ->
               Elab (FunClause Raw)
mkFromClause fn size i (n, [], Var ty) =
  pure $ MkFunClause (RApp (Var fn) !(mkFin size i)) (Var n)
mkFromClause fn size i (n, _, ty) =
  fail [TextPart "unsupported constructor", NamePart n]


mkOk1Clause : TTName -> (size, i : Nat) -> (constr : (TTName, List CtorArg, Raw)) -> Elab (FunClause Raw)
mkOk1Clause fn size i (n, [], Var ty) =
  pure $ MkFunClause (RApp (Var fn) (Var n))
                       [| (Var (UN "Refl")) (Var ty) (Var n) |]
mkOk1Clause fn size i (n, _, ty) =
  fail [TextPart "unsupported constructor", NamePart n]


mkOk2Clause : TTName -> (size, i : Nat) -> (constr : (TTName, List CtorArg, Raw)) -> Elab (FunClause Raw)
mkOk2Clause fn size i (n, [], Var ty) =
  pure $ MkFunClause (RApp (Var fn) !(mkFin size i))
                       [| (Var `{Refl}) `(Fin ~(quote size))
                                        !(mkFin size i) |]
mkOk2Clause fn size i (n, _, ty) =
  fail [TextPart "unsupported constructor", NamePart n]


mkToClauses : TTName -> Nat -> List (TTName, List CtorArg, Raw) -> Elab (List (FunClause Raw))
mkToClauses fn size xs = mkToClauses' Z xs
  where mkToClauses' : Nat -> List (TTName, List CtorArg, Raw) -> Elab (List (FunClause Raw))
        mkToClauses' k []        = pure []
        mkToClauses' k (x :: xs) = do rest <- mkToClauses' (S k) xs
                                      clause <- mkToClause fn size k x
                                      pure $ clause :: rest

||| Generate a clause for the end of a pattern-match on Fins that
||| declares its own impossibility.
|||
||| This is to satisfy the totality checker, because `impossible`
||| clauses are still
mkAbsurdFinClause : (fn : TTName) -> (goal : Raw -> Raw) -> (size : Nat) ->
                    Elab (FunClause Raw)
mkAbsurdFinClause fn goal size =
  do pv <- gensym "badfin"
     lhsArg <- lhsBody pv size
     let lhs = RBind pv (PVar `(Fin Z : Type))
                     (RApp (Var fn) lhsArg)
     let rhs = RBind pv (PVar `(Fin Z : Type))
                     `(FinZElim {a=~(goal lhsArg)} ~(Var pv))
     pure $ MkFunClause lhs rhs
  where lhsBody : TTName -> Nat -> Elab Raw
        lhsBody f Z = pure $ Var f
        lhsBody f (S k) = do smaller <- lhsBody f k
                             pure `(FS {k=~(quote k)} ~smaller)


mkFromClauses : TTName -> TTName -> Nat ->
                List (TTName, List CtorArg, Raw) -> Elab (List (FunClause Raw))
mkFromClauses fn ty size xs = mkFromClauses' Z xs
  where mkFromClauses' : Nat -> List (TTName, List CtorArg, Raw) -> Elab (List (FunClause Raw))
        mkFromClauses' k []        =
             pure [!(mkAbsurdFinClause fn (const (Var ty)) size)]
        mkFromClauses' k (x :: xs) = do rest <- mkFromClauses' (S k) xs
                                        clause <- mkFromClause fn size k x
                                        pure $ clause :: rest

mkOk1Clauses : TTName -> Nat -> List (TTName, List CtorArg, Raw) -> Elab (List (FunClause Raw))
mkOk1Clauses fn size xs = mkOk1Clauses' Z xs
  where mkOk1Clauses' : Nat -> List (TTName, List CtorArg, Raw) -> Elab (List (FunClause Raw))
        mkOk1Clauses' k []        = pure []
        mkOk1Clauses' k (x :: xs) = do rest <- mkOk1Clauses' (S k) xs
                                       clause <- mkOk1Clause fn size k x
                                       pure $ clause :: rest

mkOk2Clauses : TTName -> Nat -> List (TTName, List CtorArg, Raw) -> (Raw -> Raw) -> Elab (List (FunClause Raw))
mkOk2Clauses fn size xs resTy = mkOk2Clauses' Z xs
  where mkOk2Clauses' : Nat -> List (TTName, List CtorArg, Raw) -> Elab (List (FunClause Raw))
        mkOk2Clauses' k []        = pure [!(mkAbsurdFinClause fn resTy size)]
        mkOk2Clauses' k (x :: xs) = do rest <- mkOk2Clauses' (S k) xs
                                       clause <- mkOk2Clause fn size k x
                                       pure $ clause :: rest


genToFin : (to, from, ok1, ok2, ty : TTName) -> Elab ()
genToFin to from ok1 ok2 ty =
  do (MkDatatype famn tcargs tcres constrs) <- lookupDatatypeExact ty
     let size = length constrs
     argn <- gensym "arg"
     declareType $ Declare to [MkFunArg argn (Var ty) Explicit NotErased]
                           `(Fin ~(quote size))
     toClauses <- mkToClauses to size constrs
     defineFunction $ DefineFun to toClauses

     argn' <- gensym "arg"
     declareType $ Declare from [MkFunArg argn' `(Fin ~(quote size)) Explicit NotErased ]
                           (Var ty)
     fromClauses <- mkFromClauses from ty size constrs
     defineFunction $ DefineFun from fromClauses

     argn'' <- gensym "arg"
     declareType $ Declare ok1 [MkFunArg argn'' (Var ty) Explicit NotErased]
                           `((=) {A=~(Var ty)} {B=~(Var ty)}
                                 ~(RApp (Var from) (RApp (Var to) (Var argn'')))
                                 ~(Var argn''))
     ok1Clauses <- mkOk1Clauses ok1 size constrs
     defineFunction $ DefineFun ok1 ok1Clauses

     argn''' <- gensym "arg"
     let fty : Raw = `(Fin ~(quote size))
     let ok2ResTy = the (Raw -> Raw)
       (\n => `((=) {A=~fty} {B=~fty}
                   ~(RApp (Var to) (RApp (Var from) n))
                   ~n))
     declareType $ Declare ok2 [MkFunArg argn''' fty Explicit NotErased]
                           (ok2ResTy (Var argn'''))
     ok2Clauses <- mkOk2Clauses ok2 size constrs ok2ResTy
     defineFunction $ DefineFun ok2 ok2Clauses

     pure ()


deriveFinite : Elab ()
deriveFinite =
  do (App (App (P _ `{Finite} _) (P _ tyn _)) _) <- snd <$> getGoal
          | ty => fail [TextPart "inapplicable goal type", TermPart ty]
     (MkDatatype _ _ _ constrs) <- lookupDatatypeExact tyn
     let size = length constrs
     let to = SN (MetaN tyn (UN "toFinite"))
     let from = SN (MetaN tyn (UN "fromFinite"))
     let ok1 = SN (MetaN tyn (UN "finiteOk1"))
     let ok2 = SN (MetaN tyn (UN "finiteOk2"))
     genToFin to from ok1 ok2 tyn
     fill `(IsFinite {a=~(Var tyn)} {n=~(quote size)}
                     ~(Var to) ~(Var from)
                     ~(Var ok1) ~(Var ok2))
     solve

data TwoStateModel = Alive | Dead
data ThreeStateModel = Working | Disabled | Deceased


twoStateFinite : Finite TwoStateModel 2
twoStateFinite = %runElab deriveFinite

threeStateFinite : Finite ThreeStateModel 3
threeStateFinite = %runElab deriveFinite

boolFinite : Finite Bool 2
boolFinite = %runElab deriveFinite

module Reflect

import Decidable.Equality

%access public export
%default total
%language FirstClassReflection

using (xs : List a, ys : List a, gam : List (List a))

  data Elem : a -> List a -> Type where
       Stop : Elem x (x :: xs)
       Pop  : Elem x ys -> Elem x (y :: ys)

-- Expr is a reflection of a list, indexed over the concrete list,
-- and over a set of list variables.

  data Expr : List (List a) -> List a -> Type where
       App  : Expr gam xs -> Expr gam ys -> Expr gam (xs ++ ys)
       Var  : Elem xs gam -> Expr gam xs
       ENil : Expr gam []

-- Reflection of list equalities, indexed over the concrete equality.

  data ListEq : List (List a) -> Type -> Type where
       EqP : Expr gam xs -> Expr gam ys -> ListEq gam (xs = ys)

-- Fully right associative list expressions

  data RExpr : List (List a) -> List a -> Type where
       RApp : RExpr gam xs -> Elem ys gam -> RExpr gam (xs ++ ys)
       RNil : RExpr gam []

-- Convert an expression to a right associative expression, and return
-- a proof that the rewriting has an equal interpretation to the original
-- expression.

-- The idea is that we use this proof to build a proof of equality of
-- list appends

  expr_r : Expr gam xs -> (xs' ** (RExpr gam xs', xs = xs'))
  expr_r ENil = (_ ** (RNil, Refl))
  expr_r (Var i) = (_ ** (RApp RNil i, Refl))
  expr_r (App ex ey) = let (xl ** (xr, xprf)) = expr_r ex in
                       let (yl ** (yr, yprf)) = expr_r ey in
                               appRExpr _ _ xr yr xprf yprf
    where
      appRExpr : (xs', ys' : List a) ->
                 {gam : List (List a)} -> {xs, ys : List a} ->
                 RExpr gam xs -> RExpr gam ys -> (xs' = xs) -> (ys' = ys) ->
                 (ws' ** (RExpr gam ws', xs' ++ ys' = ws'))
      appRExpr x' y' rxs (RApp e i) xprf yprf
         = let (xs ** (rec, prf)) = appRExpr _ _ rxs e Refl Refl in
               (_ ** (RApp rec i, ?appRExpr1))
      appRExpr x' y' rxs RNil xprf yprf = (_ ** (rxs, ?appRExpr2))

  r_expr : RExpr gam xs -> Expr gam xs
  r_expr RNil = ENil
  r_expr (RApp xs i) = App (r_expr xs) (Var i)

-- Convert an expression to some other equivalent expression (which
-- just happens to be normalised to right associative form)

  reduce : Expr gam xs -> (xs' ** (Expr gam xs', xs = xs'))
  reduce e = let (x' ** (e', prf)) = expr_r e in
                 (x' ** (r_expr e', prf))

-- Build a proof that two expressions are equal. If they are, we'll know
-- that the indices are equal.

  eqExpr : (e : Expr gam xs) -> (e' : Expr gam ys) ->
           Maybe (e = e')
  eqExpr (App x y) (App x' y') with (eqExpr x x', eqExpr y y')
    eqExpr (App x y) (App x y)   | (Just Refl, Just Refl) = Just Refl
    eqExpr (App x y) (App x' y') | _ = Nothing
  eqExpr (Var i) (Var j) with (prim__syntactic_eq _ _ i j)
    eqExpr (Var i) (Var i) | (Just Refl) = Just Refl
    eqExpr (Var i) (Var j) | _ = Nothing
  eqExpr ENil ENil = Just Refl
  eqExpr _ _ = Nothing

-- Given a couple of reflected expressions, try to produce a proof that
-- they are equal

  buildProof : {xs : List a} -> {ys : List a} ->
               Expr gam ln -> Expr gam rn ->
               (xs = ln) -> (ys = rn) -> Maybe (xs = ys)
  buildProof e e' lp rp with (eqExpr e e')
    buildProof e e lp rp  | Just Refl = ?bp1
    buildProof e e' lp rp | Nothing = Nothing

  testEq : Expr gam xs -> Expr gam ys -> Maybe (xs = ys)
  testEq l r = let (ln ** (l', lPrf)) = reduce l in
               let (rn ** (r', rPrf)) = reduce r in
                   buildProof l' r' lPrf rPrf

-- Given a reflected equality, try to produce a proof that holds

  prove : ListEq gam t -> Maybe t
  prove (EqP xs ys) = testEq xs ys

  getJust : (x : Maybe a) -> IsJust x -> a
  getJust (Just p) ItIsJust = p


-- Some helpers for later... 'prim__syntactic_eq' is a primitive which
-- (at compile-time only) attempts to construct a proof that its arguments
-- are syntactically equal. We'll find this useful for referring to variables
-- in reflected terms.

  isElem : (x : a) -> (xs : List a) -> Maybe (Elem x xs)
  isElem x [] = Nothing
  isElem x (y :: ys) with (prim__syntactic_eq _ _ x y)
    isElem x (x :: ys) | Just Refl = [| Stop |]
    isElem x (y :: ys) | Nothing = [| Pop (isElem x ys) |]

  weakenElem : (gam' : List a) -> Elem x xs -> Elem x (gam' ++ xs)
  weakenElem [] p = p
  weakenElem (g :: gam) p = Pop (weakenElem gam p)

  weaken : (gam' : List (List a)) ->
           Expr gam xs -> Expr (gam' ++ gam) xs
  weaken gam' (App l r) = App (weaken gam' l) (weaken gam' r)
  weaken gam' (Var x) = Var (weakenElem gam' x)
  weaken gam' ENil = ENil


-- Now, some reflection magic.
-- %reflection means a function runs on syntax, rather than on constructors.
-- So, 'reflectList' builds a reflected List expression as defined above.

-- It also converts (x :: xs) into a reflected [x] ++ xs So that the above
-- reduction will work the right way.

%reflection
reflectList : (gam : List (List a)) ->
          (xs : List a) -> (gam' ** Expr (gam' ++ gam) xs)
reflectList gam [] = ([] ** ENil)

reflectList gam (x :: xs) with (reflectList gam xs)
     | (gam' ** xs') with (isElem (List.(::) x []) (gam' ++ gam))
        | Just p = (gam' ** App (Var p) xs')
        | Nothing = ([x] :: gam' ** App (Var Stop) (weaken [[x]] xs'))

reflectList gam (xs ++ ys) with (reflectList gam xs)
     | (gam' ** xs') with (reflectList (gam' ++ gam) ys)
         | (gam'' ** ys') = ((gam'' ++ gam') **
                              rewrite (sym (appendAssociative gam'' gam' gam)) in
                                 App (weaken gam'' xs') ys')
reflectList gam t with (isElem t gam)
            | Just p = ([] ** Var p)
            | Nothing = ([t] ** Var Stop)


-- Similarly, reflectEq converts an equality proof on Lists into the ListEq
-- reflection. Note that it isn't total, and we have to give the element type
-- explicitly because it can't be inferred from P.

-- This is not really a problem - we'll want different reflections for different
-- forms of equality proofs anyway.

%reflection
reflectEq : (a : Type) -> (gam : List (List a)) -> (P : Type) -> (gam' ** ListEq (gam' ++ gam) P)
reflectEq a gam (the (List a) xs = the (List a) ys) with (reflectList gam xs)
     | (gam' ** xs')  with (reflectList (gam' ++ gam) ys)
        | (gam'' ** ys') = ((gam'' ++ gam') **
                           rewrite (sym (appendAssociative gam'' gam' gam)) in
                               EqP (weaken gam'' xs') ys')


-- Need these before we can test it or the reductions won't normalise fully...

---------- Proofs ----------

Reflect.appRExpr1 = proof {
  intros;
  rewrite sym xprf;
  rewrite sym yprf;
  rewrite prf;
  rewrite sym (appendAssociative xs2 xs3 ys1);
  trivial;
}

Reflect.appRExpr2 = proof {
  intros;
  rewrite xprf;
  rewrite sym yprf;
  rewrite appendNilRightNeutral x';
  trivial;
}

Reflect.bp1 = proof {
  intros;
  refine Just;
  rewrite sym lp;
  rewrite sym rp;
  trivial;
}

-- "quoteGoal x by p in e" does some magic
-- The effect is to bind x to p applied to the current goal. If 'p' is a
-- reflection function (which is the most likely thing to be useful...)
-- then we can feed the result to the above 'prove' function and pull out
-- the proof, if it exists.

-- The syntax declaration below just gives us an easy way to invoke the
-- prover.

syntax AssocProof [ty] = quoteGoal x by reflectEq ty [] in
                             getJust (prove (snd x)) ItIsJust

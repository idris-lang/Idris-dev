||| Internal details of the library, not for public consumption.
module Pruviloj.Internals


import Pruviloj.Core
import Pruviloj.Renamers

import Data.Vect

||| Get the name of a reflected type constructor argument.
tyConArgName : TyConArg -> TTName
tyConArgName (TyConParameter a) = argName a
tyConArgName (TyConIndex a) = argName a

||| Modify the name of a reflected type constructor argument.
setTyConArgName : TyConArg -> TTName -> TyConArg
setTyConArgName (TyConParameter a) n = TyConParameter (record {argName = n} a)
setTyConArgName (TyConIndex a) n = TyConIndex (record {argName = n} a)

||| Modify the type of a reflected type constructor argument using some function.
updateTyConArgTy : (Raw -> Raw) -> TyConArg -> TyConArg
updateTyConArgTy f (TyConParameter a) =
    TyConParameter (record {argTy = f (argTy a) } a)
updateTyConArgTy f (TyConIndex a) =
    TyConIndex (record {argTy = f (argTy a) } a)

unApply : Raw -> (Raw, List Raw)
unApply tm = unApply' tm []
  where unApply' : Raw -> List Raw -> (Raw, List Raw)
        unApply' (RApp f x) xs = unApply' f (x::xs)
        unApply' notApp xs = (notApp, xs)

mkApp : Raw -> List Raw -> Raw
mkApp f [] = f
mkApp f (x :: xs) = mkApp (RApp f x) xs

||| Grab the binders from around a term, alpha-converting to make
||| their names unique
partial
stealBindings : Raw -> (nsubst : TTName -> Maybe TTName) -> Elab (List (TTName, Binder Raw), Raw)
stealBindings (RBind n b tm) nsubst =
  do n' <- nameFrom n
     (bindings, result) <- stealBindings tm (extend nsubst n n')
     return ((n', map (alphaRaw nsubst) b) :: bindings, result)
stealBindings tm nsubst = return ([], alphaRaw nsubst tm)

||| Get the last element of a list. Fail on empty lists.
last : List a -> Elab a
last [] = fail [TextPart "Unexpected empty list"]
last [x] = return x
last (_::x::xs) = last (x::xs)

||| Grab the binders from around a term, assuming that they have been
||| previously uniquified
extractBinders : Raw -> (List (TTName, Binder Raw), Raw)
extractBinders (RBind n b tm) = let (bs, res) = extractBinders tm
                                in ((n, b) :: bs, res)
extractBinders tm = ([], tm)


||| Get the type annotation from a binder
getBinderTy : Binder t -> t
getBinderTy (Lam t) = t
getBinderTy (Pi t _) = t
getBinderTy (Let t _) = t
getBinderTy (Hole t) = t
getBinderTy (GHole t) = t
getBinderTy (Guess t _) = t
getBinderTy (PVar t) = t
getBinderTy (PVTy t) = t

||| Map a list `[x1, x2, ..., xn]` to `[(0, x1), (1, x2), ..., (n-1, xn)]`
enumerate : List a -> List (Nat, a)
enumerate xs = enumerate' xs 0
  where enumerate' : List a -> Nat -> List (Nat, a)
        enumerate' [] _ = []
        enumerate' (x::xs) n = (n, x) :: enumerate' xs (S n)

bindPats : List (TTName, Binder Raw) -> Raw -> Raw
bindPats [] res = res
bindPats ((n, b)::bs) res = RBind n (PVar (getBinderTy b)) $ bindPats bs res

bindPatTys : List (TTName, Binder Raw) -> Raw -> Raw
bindPatTys [] res = res
bindPatTys ((n, b)::bs) res = RBind n (PVTy (getBinderTy b)) $ bindPatTys bs res


||| Helper for elaborating pattern clauses. This helper takes care of
||| inferring the type of the left-hand side and bringing that
||| information onward to the right-hand side.
|||
||| While elaborating the left-hand side, the proof term contains a
||| Sigma type. This is part of the type inference going on and will
||| be removed.
|||
||| @ lhs the tactic script to establish the left-hand side of the
|||       clause. It should cause an application of the term being
|||       defined. Any holes left behind will be converted to pattern
|||       variables with the same name.
||| @ rhs the tactic script to establish the right side of the clause.
|||       It will be run in a context where the pattern variables are
|||       already bound, and should leave behind no holes.
partial
elabPatternClause : (lhs, rhs : Elab ()) -> Elab FunClause
elabPatternClause lhs rhs =
  do -- Elaborate the LHS in a context where its type will be solved via unification
     (pat, _) <- runElab `(Infer) $
                    do th <- newHole "finalTy" `(Type)
                       patH <- newHole "pattern" (Var th)
                       fill `(MkInfer ~(Var th) ~(Var patH))
                       solve
                       focus patH
                       lhs
                       -- Convert all remaining holes to pattern variables
                       traverse_ {b=()} (\h => focus h *> patvar h) !getHoles
     (pvars, `(MkInfer ~rhsTy ~lhsTm)) <- extractBinders <$> (forgetTypes pat)
        | fail [TextPart "Couldn't infer type of left-hand pattern"]
     rhsTm <- runElab (bindPatTys pvars rhsTy) $
                do -- Introduce all the pattern variables from the LHS
                   repeatUntilFail bindPat <|> return ()
                   rhs
     realRhs <- forgetTypes (fst rhsTm)
     return $ MkFunClause (bindPats pvars lhsTm) realRhs

||| Introduce a unique binder name, returning it
intro1 : Elab TTName
intro1 = do g <- snd <$> getGoal
            case g of
              Bind n (Pi _ _) _ => do n' <- nameFrom n
                                      intro n'
                                      return n'
              _ => fail [ TextPart "Can't intro1 because goal"
                        , TermPart g
                        , TextPart "isn't a function type."]


||| Repeat an action some number of times, saving the results.
doTimes : Applicative m => (n : Nat) -> m a -> m (Vect n a)
doTimes Z     x = pure []
doTimes (S k) x = [| x :: (doTimes k x) |]

||| Zip two lists, failing if their lengths don't match.
zipH : List a -> List b -> Elab (List (a, b))
zipH [] [] = return []
zipH (x::xs) (y::ys) = ((x, y) ::) <$> zipH xs ys
zipH _ _ = fail [TextPart "length mismatch"]

unsafeNth : Nat -> List a -> Elab a
unsafeNth _     []        = fail [TextPart "Ran out of list elements"]
unsafeNth Z     (x :: _)  = return x
unsafeNth (S k) (_ :: xs) = unsafeNth k xs



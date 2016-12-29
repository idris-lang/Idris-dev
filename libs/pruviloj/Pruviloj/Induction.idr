module Pruviloj.Induction

import Language.Reflection.Utils

import Pruviloj.Core
import Pruviloj.Derive.Eliminators
import Pruviloj.Internals.TyConInfo
import Pruviloj.Internals
import Pruviloj.Renamers


%access private

-- To perform induction:
--  1. Type check the thing to do induction on
--  2. If its type is not an inductive family, error
--  3. Ensure that there exists an eliminator for the family
--  4. Abstract the goal over the scrutinee to get the motive
--  5. Apply the eliminator to the scrutinee and motive, with holes for methods
--  6. Return these holes


elimN : TTName -> TTName
elimN n = NS (SN $ MetaN (UN "elim") n) ["Eliminators", "Induction", "Pruviloj"]

mutual
  alphaEqual : (subst : TTName -> Maybe TTName) -> Raw -> Raw -> Bool
  alphaEqual subst (Var n) (Var m)  =
    case subst n of
      Just n' => n' == m -- both are bound if this has been put in the subst
      Nothing => n == m -- free
  alphaEqual subst (RBind n b tm) (RBind m b' tm') =
      alphaEqualBinders subst b b' &&
      alphaEqual (extend subst n m) tm tm'
  alphaEqual subst (RApp f x) (RApp g y) =
      alphaEqual subst f g && alphaEqual subst x y
  alphaEqual subst RType RType  = True
  alphaEqual subst (RUType u) (RUType u') = u == u'
  alphaEqual subst (RConstant c) (RConstant c')  = c == c'
  alphaEqual subst _ _ = False

  alphaEqualBinders : (subst : TTName -> Maybe TTName) -> Binder Raw -> Binder Raw -> Bool
  alphaEqualBinders subst (Lam tm) (Lam tm') =
      alphaEqual subst tm tm'
  alphaEqualBinders subst (Pi tm1 tm2) (Pi tm1' tm2') =
      alphaEqual subst tm1 tm1' &&
      alphaEqual subst tm2 tm2'
  alphaEqualBinders subst (Let tm1 tm2) (Let tm1' tm2') =
      alphaEqual subst tm1 tm1' &&
      alphaEqual subst tm2 tm2'
  alphaEqualBinders subst (Hole tm) (Hole tm') =
      alphaEqual subst tm tm'
  alphaEqualBinders subst (GHole tm) (GHole tm') =
      alphaEqual subst tm tm'
  alphaEqualBinders subst (Guess tm1 tm2) (Guess tm1' tm2') =
      alphaEqual subst tm1 tm1' &&
      alphaEqual subst tm2 tm2'
  alphaEqualBinders subst (PVar tm) (PVar tm') =
      alphaEqual subst tm tm'
  alphaEqualBinders subst (PVTy tm) (PVTy tm') =
      alphaEqual subst tm tm'
  alphaEqualBinders subst _ _ = False

generalize : (hint : String) -> (ctxt, subject : Raw) -> Elab (TTName, Raw)
generalize hint ctxt subj = do n <- gensym hint
                               pure (n, !(gen' n ctxt subj))
  where
    mutual
      gen' : TTName -> Raw -> Raw -> Elab Raw
      gen' var outer inner = if alphaEqual (const Nothing) outer inner
                               then pure (Var var)
                               else breakAndRecurse var outer inner

      genB : TTName -> Binder Raw -> Raw -> Elab (Binder Raw)
      genB n (Lam ty)       inner = [| Lam (gen' n ty inner) |]
      genB n (Pi ty ty')    inner = [| Pi (gen' n ty inner) (gen' n ty' inner) |]
      genB n (Let ty val)   inner = [| Let (gen' n ty inner) (gen' n val inner) |]
      genB n (Hole ty)      inner = [| Hole (gen' n ty inner) |]
      genB n (GHole ty)     inner = [| GHole (gen' n ty inner) |]
      genB n (Guess ty val) inner = [| Guess (gen' n ty inner) (gen' n val inner) |]
      genB n (PVar ty)      inner = [| PVar (gen' n ty inner) |]
      genB n (PVTy ty)      inner = [| PVTy (gen' n ty inner) |]

      breakAndRecurse : TTName -> Raw -> Raw -> Elab Raw
      breakAndRecurse var (RBind n b tm) inner =
          -- Prevent variable capture by alpha-converting to a unique name
          do n' <- nameFrom n
             b' <- genB var b inner
             body' <- gen' var (alphaRaw (rename n n') tm) inner
             pure $ RBind n' b' body'
      breakAndRecurse var (RApp tm tm') inner =
          [| RApp (gen' var tm inner) (gen' var tm' inner) |]
      breakAndRecurse var other inner = pure other


countBinders : TT -> Nat
countBinders (Bind _ _ tm) = S (countBinders tm)
countBinders _ = Z



indexVals : Raw -> TyConInfo -> List Raw
indexVals tm info =
  do let (var, tyArgs) = unApply tm
     let argsTogether = zip tyArgs (args info)
     (argVal, TyConIndex _) <- argsTogether
             | _ => empty
     pure argVal

makeMotive : (info : TyConInfo) -> (subj, subjTy, goal : Raw) -> Elab ()
makeMotive info sub subjTy goal =
    makeMotive' (indexVals subjTy info) goal
  where
    makeMotive' : List Raw -> Raw -> Elab ()
    makeMotive' [] r = do (n, r') <- generalize "subj" r sub
                          attack
                          intro n
                          exact r'
                          solve -- attack
    makeMotive' (i :: is) r = do (n, r') <- generalize "i" r i
                                 attack
                                 intro n
                                 makeMotive' is r'
                                 solve --attack

||| Perform induction on some expression to solve the current
||| goal. Return a list of new holes to be solved.
public export
induction : Raw -> Elab (List TTName)
induction subj =
    do g <- goalType
       (_, ty) <- check !getEnv subj
       ty' <- forget ty
       case headName ty' of
         Nothing =>
           fail [TermPart ty,
                 TextPart "is not a datatype declared with the data keyword"]
         Just fam =>
           do let elim = elimN fam
              (_,_,elimTy) <- (lookupTyExact elim) <|> (do deriveElim fam elim
                                                           lookupTyExact elim)
              tydef <- lookupDatatypeExact fam
              info <- getTyConInfo (tyConArgs tydef) (tyConRes tydef)
              argHoles <- apply (Var elim)
                                (replicate (length (args info)) True ++
                                 [False, False] ++ -- scrutinee, motive
                                 replicate (length (constructors tydef)) False)
              solve

              -- Apply the eliminator to our scrutinee
              scrutH <- unsafeNth (length (args info)) argHoles
              focus scrutH
              apply subj []
              solve

              motiveH <- unsafeNth (length (args info) + 1) argHoles
              focus motiveH; makeMotive info subj ty' g

              pure (drop (2 + length (tyConArgs tydef)) argHoles)

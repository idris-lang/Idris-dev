{-# LANGUAGE PatternGuards #-}

module Idris.Delaborate where

-- Convert core TT back into high level syntax, primarily for display
-- purposes.

import Idris.AbsSyntax
import Core.TT

import Debug.Trace

bugaddr = "https://github.com/edwinb/Idris-dev/issues"

delab :: IState -> Term -> PTerm
delab i tm = delab' i tm False

delab' :: IState -> Term -> Bool -> PTerm
delab' ist tm fullname = de [] tm
  where
    un = FC "(val)" 0

    de env (App f a) = deFn env f [a]
    de env (V i)     | i < length env = PRef un (snd (env!!i))
                     | otherwise = PRef un (UN ("v" ++ show i ++ ""))
    de env (P _ n _) | n == unitTy = PTrue un
                     | n == unitCon = PTrue un
                     | n == falseTy = PFalse un
                     | Just n' <- lookup n env = PRef un n'
                     | otherwise = PRef un (dens n)
    de env (Bind n (Lam ty) sc) = PLam n (de env ty) (de ((n,n):env) sc)
    de env (Bind n (Pi ty) sc)  = PPi expl n (de env ty) (de ((n,n):env) sc)
    de env (Bind n (Let ty val) sc) 
        = PLet n (de env ty) (de env val) (de ((n,n):env) sc)
    de env (Bind n (Hole ty) sc) = de ((n, UN "[__]"):env) sc
    de env (Bind n (Guess ty val) sc) = de ((n, UN "[__]"):env) sc
    de env (Bind n _ sc) = de ((n,n):env) sc
    de env (Constant i) = PConstant i
    de env Erased = Placeholder
    de env Impossible = Placeholder
    de env (TType i) = PType 

    dens x | fullname = x
    dens ns@(NS n _) = case lookupCtxt Nothing n (idris_implicits ist) of
                              [_] -> n -- just one thing
                              _ -> ns
    dens n = n

    deFn env (App f a) args = deFn env f (a:args)
    deFn env (P _ n _) [l,r]     | n == pairTy  = PPair un (de env l) (de env r)
                                 | n == eqCon   = PRefl un (de env r)
                                 | n == UN "lazy" = de env r
    deFn env (P _ n _) [ty, Bind x (Lam _) r]
                                 | n == UN "Exists" 
                                       = PDPair un (PRef un x) (de env ty)
                                                   (de ((x,x):env) (instantiate (P Bound x ty) r))
    deFn env (P _ n _) [_,_,l,r] | n == pairCon = PPair un (de env l) (de env r)
                                 | n == eqTy    = PEq un (de env l) (de env r)
                                 | n == UN "Ex_intro" = PDPair un (de env l) Placeholder
                                                                  (de env r)
    deFn env (P _ n _) args = mkPApp (dens n) (map (de env) args)
    deFn env f args = PApp un (de env f) (map pexp (map (de env) args))

    mkPApp n args 
        | [imps] <- lookupCtxt Nothing n (idris_implicits ist)
            = PApp un (PRef un n) (zipWith imp (imps ++ repeat (pexp undefined)) args)
        | otherwise = PApp un (PRef un n) (map pexp args)

    imp (PImp p l n _ d) arg = PImp p l n arg d
    imp (PExp p l _ d)   arg = PExp p l arg d
    imp (PConstraint p l _ d) arg = PConstraint p l arg d
    imp (PTacImplicit p l n sc _ d) arg = PTacImplicit p l n sc arg d

pshow :: IState -> Err -> String
pshow i (Msg s) = s
pshow i (InternalMsg s) = "INTERNAL ERROR: " ++ show s ++ 
   "\nThis is probably a bug, or a missing error message.\n" ++
   "Please consider reporting at " ++ bugaddr
pshow i (CantUnify _ x y e sc s) 
    = let imps = opt_showimp (idris_options i) in
        "Can't unify " ++ showImp imps (delab i x)
          ++ " with " ++ showImp imps (delab i y) ++
--         " (" ++ show x ++ " and " ++ show y ++ ") " ++
        case e of
            Msg "" -> ""
            _ -> "\n\nSpecifically:\n\t" ++ pshow i e ++ 
                 if (opt_errContext (idris_options i)) then showSc i sc else ""
pshow i (CantConvert x y env) 
    = let imps = opt_showimp (idris_options i) in
          "Can't convert " ++ showImp imps (delab i x) ++ " with " 
                 ++ showImp imps (delab i y) ++
                 if (opt_errContext (idris_options i)) then showSc i env else ""
pshow i (InfiniteUnify x tm env)
    = "Unifying " ++ showbasic x ++ " and " ++ show (delab i tm) ++ 
      " would lead to infinite value" ++
                 if (opt_errContext (idris_options i)) then showSc i env else ""
pshow i (NotInjective p x y) = "Can't verify injectivity of " ++ show (delab i p) ++
                               " when unifying " ++ show (delab i x) ++ " and " ++ 
                                                    show (delab i y)
pshow i (CantResolve c) = "Can't resolve type class " ++ show (delab i c)
pshow i (CantResolveAlts as) = "Can't disambiguate name: " ++ showSep ", " as
pshow i (NoTypeDecl n) = "No type declaration for " ++ show n
pshow i (NoSuchVariable n) = "No such variable " ++ show n
pshow i (IncompleteTerm t) = "Incomplete term " ++ showImp True (delab i t)
pshow i UniverseError = "Universe inconsistency"
pshow i ProgramLineComment = "Program line next to comment"
pshow i (Inaccessible n) = show n ++ " is not an accessible pattern variable"
pshow i (NonCollapsiblePostulate n) 
    = "The return type of postulate " ++ show n ++ " is not collapsible"
pshow i (AlreadyDefined n) = show n ++ " is already defined"
pshow i (At f e) = show f ++ ":" ++ pshow i e

showSc i [] = ""
showSc i xs = "\n\nIn context:\n" ++ showSep "\n" (map showVar (reverse xs))
  where showVar (x, y) = "\t" ++ showbasic x ++ " : " ++ show (delab i y)

showbasic n@(UN _) = show n
showbasic (MN _ s) = s
showbasic (NS n s) = showSep "." (reverse s) ++ "." ++ showbasic n

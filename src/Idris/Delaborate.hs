{-# LANGUAGE PatternGuards #-}

module Idris.Delaborate where

-- Convert core TT back into high level syntax, primarily for display
-- purposes.

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.Core.Evaluate

import Data.List (intersperse)

import Debug.Trace

bugaddr = "https://github.com/idris-lang/Idris-dev/issues"

delab :: IState -> Term -> PTerm
delab i tm = delab' i tm False False

delabMV :: IState -> Term -> PTerm
delabMV i tm = delab' i tm False True

delabTy :: IState -> Name -> PTerm
delabTy i n
    = case lookupTy n (tt_ctxt i) of
           (ty:_) -> case lookupCtxt n (idris_implicits i) of
                         (imps:_) -> delabTy' i imps ty False False
                         _ -> delabTy' i [] ty False False

delab' :: IState -> Term -> Bool -> Bool -> PTerm
delab' i t f mvs = delabTy' i [] t f mvs

delabTy' :: IState -> [PArg] -- ^ implicit arguments to type, if any
          -> Term 
          -> Bool -- ^ use full names
          -> Bool -- ^ Don't treat metavariables specially
          -> PTerm
delabTy' ist imps tm fullname mvs = de [] imps tm
  where
    un = fileFC "(val)"

    de env _ (App f a) = deFn env f [a]
    de env _ (V i)     | i < length env = PRef un (snd (env!!i))
                       | otherwise = PRef un (sUN ("v" ++ show i ++ ""))
    de env _ (P _ n _) | n == unitTy = PTrue un
                       | n == unitCon = PTrue un
                       | n == falseTy = PFalse un
                       | Just n' <- lookup n env = PRef un n'
                       | otherwise
                            = case lookup n (idris_metavars ist) of
                                  Just (Just _, mi, _) -> mkMVApp (dens n) []
                                  _ -> PRef un (dens n)
    de env _ (Bind n (Lam ty) sc)
          = PLam n (de env [] ty) (de ((n,n):env) [] sc)
    de env (PImp _ _ _ _ _ _:is) (Bind n (Pi ty) sc)
          = PPi impl n (de env [] ty) (de ((n,n):env) is sc)
    de env (PConstraint _ _ _ _:is) (Bind n (Pi ty) sc)
          = PPi constraint n (de env [] ty) (de ((n,n):env) is sc)
    de env (PTacImplicit _ _ _ tac _ _:is) (Bind n (Pi ty) sc)
          = PPi (tacimpl tac) n (de env [] ty) (de ((n,n):env) is sc)
    de env _ (Bind n (Pi ty) sc)
          = PPi expl n (de env [] ty) (de ((n,n):env) [] sc)
    de env _ (Bind n (Let ty val) sc)
        = PLet n (de env [] ty) (de env [] val) (de ((n,n):env) [] sc)
    de env _ (Bind n (Hole ty) sc) = de ((n, sUN "[__]"):env) [] sc
    de env _ (Bind n (Guess ty val) sc) = de ((n, sUN "[__]"):env) [] sc
    de env _ (Bind n _ sc) = de ((n,n):env) [] sc
    de env _ (Constant i) = PConstant i
    de env _ Erased = Placeholder
    de env _ Impossible = Placeholder
    de env _ (TType i) = PType

    dens x | fullname = x
    dens ns@(NS n _) = case lookupCtxt n (idris_implicits ist) of
                              [_] -> n -- just one thing
                              [] -> n -- metavariables have no implicits
                              _ -> ns
    dens n = n

    deFn env (App f a) args = deFn env f (a:args)
    deFn env (P _ n _) [l,r]
         | n == pairTy    = PPair un (de env [] l) (de env [] r)
         | n == eqCon     = PRefl un (de env [] r)
         | n == sUN "lazy" = de env [] r
    deFn env (P _ n _) [ty, Bind x (Lam _) r]
         | n == sUN "Exists"
               = PDPair un (PRef un x) (de env [] ty)
                           (de ((x,x):env) [] (instantiate (P Bound x ty) r))
    deFn env (P _ n _) [_,_,l,r]
         | n == pairCon = PPair un (de env [] l) (de env [] r)
         | n == eqTy    = PEq un (de env [] l) (de env [] r)
         | n == sUN "Ex_intro" = PDPair un (de env [] l) Placeholder
                                           (de env [] r)
    deFn env (P _ n _) args | not mvs
         = case lookup n (idris_metavars ist) of
                Just (Just _, mi, _) ->
                     mkMVApp (dens n) (drop mi (map (de env []) args))
                _ -> mkPApp (dens n) (map (de env []) args)
         | otherwise = mkPApp (dens n) (map (de env []) args)
    deFn env f args = PApp un (de env [] f) (map pexp (map (de env []) args))

    mkMVApp n []
            = PMetavar n
    mkMVApp n args
            = PApp un (PMetavar n) (map pexp args)
    mkPApp n args
        | [imps] <- lookupCtxt n (idris_implicits ist)
            = PApp un (PRef un n) (zipWith imp (imps ++ repeat (pexp undefined)) args)
        | otherwise = PApp un (PRef un n) (map pexp args)

    imp (PImp p m l n _ d) arg = PImp p m l n arg d
    imp (PExp p l _ d)   arg = PExp p l arg d
    imp (PConstraint p l _ d) arg = PConstraint p l arg d
    imp (PTacImplicit p l n sc _ d) arg = PTacImplicit p l n sc arg d


indented text = boxIt '\n' $ unlines $ map ('\t':) $ lines text where
    boxIt c text = (c:text) ++ if last text == c
                                  then ""
                                  else [c]

pshow :: IState -> Err -> String
pshow i (Msg s) = s
pshow i (InternalMsg s) = "INTERNAL ERROR: " ++ show s ++
   "\nThis is probably a bug, or a missing error message.\n" ++
   "Please consider reporting at " ++ bugaddr
pshow i (CantUnify _ x y e sc s)
    = let imps = opt_showimp (idris_options i) in
      let colour = idris_colourRepl i in
        "Can't unify" ++ indented (showImp (Just i) imps colour (delab i x))
          ++ "with" ++ indented (showImp (Just i) imps colour (delab i y)) ++
--         " (" ++ show x ++ " and " ++ show y ++ ") " ++
        case e of
            Msg "" -> ""
            _ -> "\nSpecifically:" ++
                indented (pshow i e) ++
                if (opt_errContext (idris_options i)) then showSc i sc else ""
pshow i (CantConvert x y env)
    = let imps = opt_showimp (idris_options i) in
      let colour = idris_colourRepl i in
          "Can't convert" ++ indented (showImp (Just i) imps colour (delab i x)) ++ "with"
                 ++ indented (showImp (Just i) imps colour (delab i y)) ++
                 if (opt_errContext (idris_options i)) then showSc i env else ""
pshow i (CantSolveGoal x env)
    = let imps = opt_showimp (idris_options i) in
      let colour = idris_colourRepl i in
          "Can't solve goal " ++ indented (showImp (Just i) imps colour (delab i x)) ++
                 if (opt_errContext (idris_options i)) then showSc i env else ""
pshow i (UnifyScope n out tm env)
    = let imps = opt_showimp (idris_options i) in
      let colour = idris_colourRepl i in
          "Can't unify" ++ indented (show n) ++ "with"
                 ++ indented (showImp (Just i) imps colour (delab i tm)) ++ "as" ++
                 indented (show out) ++ "is not in scope" ++
                 if (opt_errContext (idris_options i)) then showSc i env else ""
pshow i (CantInferType t)
    = "Can't infer type for " ++ t
pshow i (NonFunctionType f ty)
    = let imps = opt_showimp (idris_options i) in
      let colour = idris_colourRepl i in
          showImp (Just i) imps colour (delab i f) ++ " does not have a function type ("
            ++ showImp (Just i) imps colour (delab i ty) ++ ")"
pshow i (NotEquality tm ty)
    = let imps = opt_showimp (idris_options i) in
      let colour = idris_colourRepl i in
          showImp (Just i) imps colour (delab i tm) ++ " does not have an equality type ("
            ++ showImp (Just i) imps colour (delab i ty) ++ ")"
pshow i (TooManyArguments f)
    = "Too many arguments for " ++ show f
pshow i (CantIntroduce ty)
    = let imps = opt_showimp (idris_options i) in
      let colour = idris_colourRepl i in
          "Can't use lambda here: type is " ++ showImp (Just i) imps colour (delab i ty)
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
pshow i (IncompleteTerm t) = "Incomplete term " ++ showImp Nothing True False (delab i t)
pshow i UniverseError = "Universe inconsistency"
pshow i ProgramLineComment = "Program line next to comment"
pshow i (Inaccessible n) = show n ++ " is not an accessible pattern variable"
pshow i (NonCollapsiblePostulate n)
    = "The return type of postulate " ++ show n ++ " is not collapsible"
pshow i (AlreadyDefined n) = show n ++ " is already defined"
pshow i (ProofSearchFail e) = pshow i e
pshow i (NoRewriting tm) = "rewrite did not change type " ++ show (delab i tm)
pshow i (At f e) = show f ++ ":" ++ pshow i e
pshow i (Elaborating s n e) = "When elaborating " ++ s ++
                               showqual i n ++ ":\n" ++ pshow i e
pshow i (ProviderError msg) = "Type provider error: " ++ msg
pshow i (LoadingFailed fn e) = "Loading " ++ fn ++ " failed: " ++ pshow i e
pshow i (ReflectionError parts orig) = let parts' = map (concat . intersperse " " . map showPart) parts in
                                       concat (intersperse "\n" parts') ++
                                       "\nOriginal error:\n" ++ indented (pshow i orig)
      where showPart :: ErrorReportPart -> String
            showPart (TextPart str) = str
            showPart (NamePart n)   = let colour = idris_colourRepl i in
                                      showName (Just i) [] False colour n
            showPart (TermPart tm)  = let colour = idris_colourRepl i
                                      in showImp (Just i) False colour (delab i tm)
            showPart (SubReport rs) = indented . concat . intersperse " " . map showPart $ rs
pshow i (ReflectionFailed msg err) = "When attempting to perform error reflection, the following internal error occurred:\n" ++
                                     indented (pshow i err) ++
                                     "\nThis is probably a bug. Please consider reporting it at " ++ bugaddr


showSc i [] = ""
showSc i xs = "\n\nIn context:\n" ++ showSep "\n" (map showVar (reverse xs))
  where showVar (x, y) = "\t" ++ showbasic x ++ " : " ++ show (delab i y)

showqual :: IState -> Name -> String
showqual i n = showName (Just i) [] False False (dens n)
  where
    dens ns@(NS n _) = case lookupCtxt n (idris_implicits i) of
                              [_] -> n -- just one thing
                              _ -> ns
    dens n = n

showbasic n@(UN _) = show n
showbasic (MN _ s) = str s
showbasic (NS n s) = showSep "." (map str (reverse s)) ++ "." ++ showbasic n
showbasic (SN s) = show s



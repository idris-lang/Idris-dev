{-# LANGUAGE PatternGuards #-}

module Idris.Delaborate (bugaddr, delab, delab', delabMV, delabTy, delabTy', pshow, pprintErr) where

-- Convert core TT back into high level syntax, primarily for display
-- purposes.

import Util.Pretty

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.ErrReverse

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
    de env _ (P _ n _) | n == unitTy = PTrue un IsType
                       | n == unitCon = PTrue un IsTerm
                       | n == falseTy = PFalse un
                       | Just n' <- lookup n env = PRef un n'
                       | otherwise
                            = case lookup n (idris_metavars ist) of
                                  Just (Just _, mi, _) -> mkMVApp n []
                                  _ -> PRef un n
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
         | n == pairTy    = PPair un IsType (de env [] l) (de env [] r)
         | n == eqCon     = PRefl un (de env [] r)
         | n == sUN "lazy" = de env [] r
    deFn env (P _ n _) [ty, Bind x (Lam _) r]
         | n == sUN "Exists"
               = PDPair un (PRef un x) (de env [] ty)
                           (de ((x,x):env) [] (instantiate (P Bound x ty) r))
    deFn env (P _ n _) [_,_,l,r]
         | n == pairCon = PPair un IsTerm (de env [] l) (de env [] r)
         | n == eqTy    = PEq un (de env [] l) (de env [] r)
         | n == sUN "Ex_intro" = PDPair un (de env [] l) Placeholder
                                           (de env [] r)
    deFn env (P _ n _) args | not mvs
         = case lookup n (idris_metavars ist) of
                Just (Just _, mi, _) ->
                     mkMVApp n (drop mi (map (de env []) args))
                _ -> mkPApp n (map (de env []) args)
         | otherwise = mkPApp n (map (de env []) args)
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

-- | How far to indent sub-errors
errorIndent :: Int
errorIndent = 8

-- | Actually indent a sub-error - no line at end because a newline can end
-- multiple layers of indent
indented :: Doc a -> Doc a
indented = nest errorIndent . (line <>)

pprintTerm :: IState -> PTerm -> Doc OutputAnnotation
pprintTerm ist = prettyImp (opt_showimp (idris_options ist))

pshow :: IState -> Err -> String
pshow ist err = displayDecorated (consoleDecorate ist) .
                renderPretty 1.0 80 .
                fmap (fancifyAnnots ist) $ pprintErr ist err

pprintErr :: IState -> Err -> Doc OutputAnnotation
pprintErr i err = pprintErr' i (fmap (errReverse i) err)

pprintErr' i (Msg s) = text s
pprintErr' i (InternalMsg s) =
  vsep [ text "INTERNAL ERROR:" <+> text s,
         text "This is probably a bug, or a missing error message.",
         text ("Please consider reporting at " ++ bugaddr)
       ]
pprintErr' i (CantUnify _ x y e sc s) =
  text "Can't unify" <> indented (pprintTerm i (delab i x)) <$>
  text "with" <> indented (pprintTerm i (delab i y)) <>
  case e of
    Msg "" -> empty
    _ -> line <> line <> text "Specifically:" <>
         indented (pprintErr' i e) <>
         if (opt_errContext (idris_options i)) then text $ showSc i sc else empty
pprintErr' i (CantConvert x y env) =
  text "Can't convert" <> indented (pprintTerm i (delab i x)) <$>
  text "with" <> indented (pprintTerm i (delab i y)) <>
  if (opt_errContext (idris_options i)) then line <> text (showSc i env) else empty
pprintErr' i (CantSolveGoal x env) =
  text "Can't solve goal " <> indented (pprintTerm i (delab i x)) <>
  if (opt_errContext (idris_options i)) then line <> text (showSc i env) else empty
pprintErr' i (UnifyScope n out tm env) =
  text "Can't unify" <> indented (annName n) <+>
  text "with" <> indented (pprintTerm i (delab i tm)) <+>
  text "as" <> indented (annName out) <> text "is not in scope" <>
  if (opt_errContext (idris_options i)) then line <> text (showSc i env) else empty
pprintErr' i (CantInferType t) = text "Can't infer type for" <+> text t
pprintErr' i (NonFunctionType f ty) =
  pprintTerm i (delab i f) <+>
  text "does not have a function type" <+>
  parens (pprintTerm i (delab i ty))
pprintErr' i (NotEquality tm ty) =
  pprintTerm i (delab i tm) <+>
  text "does not have an equality type" <+>
  parens (pprintTerm i (delab i ty))
pprintErr' i (TooManyArguments f) = text "Too many arguments for" <+> annName f
pprintErr' i (CantIntroduce ty) =
  text "Can't use lambda here: type is" <+> pprintTerm i (delab i ty)
pprintErr' i (InfiniteUnify x tm env) =
  text "Unifying" <+> annName' x (showbasic x) <+> text "and" <+> pprintTerm i (delab i tm) <+>
  text "would lead to infinite value" <>
  if (opt_errContext (idris_options i)) then line <> text (showSc i env) else empty
pprintErr' i (NotInjective p x y) =
  text "Can't verify injectivity of" <+> pprintTerm i (delab i p) <+>
  text " when unifying" <+> pprintTerm i (delab i x) <+> text "and" <+>
  pprintTerm i (delab i y)
pprintErr' i (CantResolve c) = text "Can't resolve type class" <+> pprintTerm i (delab i c)
pprintErr' i (CantResolveAlts as) = text "Can't disambiguate name:" <+>
                                    cat (punctuate (comma <> space) (map text as))
pprintErr' i (NoTypeDecl n) = text "No type declaration for" <+> annName n
pprintErr' i (NoSuchVariable n) = text "No such variable" <+> annName n
pprintErr' i (IncompleteTerm t) = text "Incomplete term" <+> pprintTerm i (delab i t)
pprintErr' i UniverseError = text "Universe inconsistency"
pprintErr' i ProgramLineComment = text "Program line next to comment"
pprintErr' i (Inaccessible n) = annName n <+> text "is not an accessible pattern variable"
pprintErr' i (NonCollapsiblePostulate n) = text "The return type of postulate" <+>
                                           annName n <+> text "is not collapsible"
pprintErr' i (AlreadyDefined n) = annName n<+>
                                  text "is already defined"
pprintErr' i (ProofSearchFail e) = pprintErr' i e
pprintErr' i (NoRewriting tm) = text "rewrite did not change type" <+> pprintTerm i (delab i tm)
pprintErr' i (At f e) = annotate (AnnFC f) (text (show f)) <> colon <> pprintErr' i e
pprintErr' i (Elaborating s n e) = text "When elaborating" <+> text s <>
                                   annName' n (showqual i n) <> colon <$>
                                   pprintErr' i e
pprintErr' i (ProviderError msg) = text ("Type provider error: " ++ msg)
pprintErr' i (LoadingFailed fn e) = text "Loading" <+> text fn <+> text "failed:" <+>  pprintErr' i e
pprintErr' i (ReflectionError parts orig) =
  let parts' = map (hsep . map showPart) parts in
  vsep parts' <>
  if (opt_origerr (idris_options i))
    then line <> line <> text "Original error:" <$> indented (pprintErr' i orig)
    else empty
  where showPart :: ErrorReportPart -> Doc OutputAnnotation
        showPart (TextPart str) = text str
        showPart (NamePart n)   = annName n
        showPart (TermPart tm)  = pprintTerm i (delab i tm)
        showPart (SubReport rs) = indented . hsep . map showPart $ rs
pprintErr' i (ReflectionFailed msg err) =
  text "When attempting to perform error reflection, the following internal error occurred:" <>
  indented (pprintErr' i err) <>
  text ("This is probably a bug. Please consider reporting it at " ++ bugaddr)

annName :: Name -> Doc OutputAnnotation
annName n = annName' n (show n)

annName' :: Name -> String -> Doc OutputAnnotation
annName' n str = annotate (AnnName n Nothing Nothing) (text str)

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



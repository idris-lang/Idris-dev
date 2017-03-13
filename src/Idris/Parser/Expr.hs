{-|
Module      : Idris.Parser.Expr
Description : Parse Expressions.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE ConstraintKinds, GeneralizedNewtypeDeriving, PatternGuards,
             TupleSections #-}
module Idris.Parser.Expr where

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.DSL
import Idris.Parser.Helpers
import Idris.Parser.Ops

import Prelude hiding (pi)

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import qualified Data.ByteString.UTF8 as UTF8
import Data.Char
import Data.Function (on)
import qualified Data.HashSet as HS
import Data.List
import qualified Data.List.Split as Spl
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T
import Debug.Trace
import qualified Text.Parser.Char as Chr
import Text.Parser.Expression
import Text.Parser.LookAhead
import qualified Text.Parser.Token as Tok
import qualified Text.Parser.Token.Highlight as Hi
import Text.Trifecta hiding (Err, char, charLiteral, natural, span, string,
                      stringLiteral, symbol, whiteSpace)
import Text.Trifecta.Delta

-- | Allow implicit type declarations
allowImp :: SyntaxInfo -> SyntaxInfo
allowImp syn = syn { implicitAllowed = True,
                     constraintAllowed = False }

-- | Disallow implicit type declarations
disallowImp :: SyntaxInfo -> SyntaxInfo
disallowImp = scopedImp

-- | Implicits hare are scoped rather than top level
scopedImp :: SyntaxInfo -> SyntaxInfo
scopedImp syn = syn { implicitAllowed = False,
                      constraintAllowed = False }

-- | Allow scoped constraint arguments
allowConstr :: SyntaxInfo -> SyntaxInfo
allowConstr syn = syn { constraintAllowed = True }

{-| Parses an expression as a whole
@
  FullExpr ::= Expr EOF_t;
@
 -}
fullExpr :: SyntaxInfo -> IdrisParser PTerm
fullExpr syn = do x <- expr syn
                  eof
                  i <- get
                  return $ debindApp syn (desugar syn i x)

tryFullExpr :: SyntaxInfo -> IState -> String -> Either Err PTerm
tryFullExpr syn st input =
  case runparser (fullExpr syn) st "" input of
    Success tm -> Right tm
    Failure e -> Left (Msg (show e))

{- | Parses an expression
@
  Expr ::= Pi
@
 -}
expr :: SyntaxInfo -> IdrisParser PTerm
expr = pi

{- | Parses an expression with possible operator applied
@
  OpExpr ::= {- Expression Parser with Operators based on Expr' -};
@
-}
opExpr :: SyntaxInfo -> IdrisParser PTerm
opExpr syn = do i <- get
                buildExpressionParser (table (idris_infixes i))
                                      (expr' syn)

{- | Parses either an internally defined expression or
    a user-defined one
@
Expr' ::=  "External (User-defined) Syntax"
      |   InternalExpr;
@
 -}
expr' :: SyntaxInfo -> IdrisParser PTerm
expr' syn = try (externalExpr syn)
            <|> internalExpr syn
            <?> "expression"

{- | Parses a user-defined expression -}
externalExpr :: SyntaxInfo -> IdrisParser PTerm
externalExpr syn = do i <- get
                      (FC fn start _) <- getFC
                      expr <- extensions syn (syntaxRulesList $ syntax_rules i)
                      (FC _ _ end) <- getFC
                      let outerFC = FC fn start end
                      return (mapPTermFC (fixFC outerFC) (fixFCH fn outerFC) expr)
                   <?> "user-defined expression"
  where -- Fix non-highlighting FCs by approximating with the span of the syntax application
        fixFC outer inner | inner `fcIn` outer = inner
                          | otherwise          = outer
        -- Fix highlighting FCs by making them useless, to avoid spurious highlights
        fixFCH fn outer inner | inner `fcIn` outer = inner
                              | otherwise          = FileFC fn

{- | Parses a simple user-defined expression -}
simpleExternalExpr :: SyntaxInfo -> IdrisParser PTerm
simpleExternalExpr syn = do i <- get
                            extensions syn (filter isSimple (syntaxRulesList $ syntax_rules i))
  where
    isSimple (Rule (Expr x:xs) _ _) = False
    isSimple (Rule (SimpleExpr x:xs) _ _) = False
    isSimple (Rule [Keyword _] _ _) = True
    isSimple (Rule [Symbol _]  _ _) = True
    isSimple (Rule (_:xs) _ _) = case last xs of
        Keyword _ -> True
        Symbol _  -> True
        _ -> False
    isSimple _ = False

{- | Tries to parse a user-defined expression given a list of syntactic extensions -}
extensions :: SyntaxInfo -> [Syntax] -> IdrisParser PTerm
extensions syn rules = extension syn [] (filter isValid rules)
                       <?> "user-defined expression"
  where
    isValid :: Syntax -> Bool
    isValid (Rule _ _ AnySyntax) = True
    isValid (Rule _ _ PatternSyntax) = inPattern syn
    isValid (Rule _ _ TermSyntax) = not (inPattern syn)
    isValid (DeclRule _ _) = False

data SynMatch = SynTm PTerm | SynBind FC Name -- ^ the FC is for highlighting information
  deriving Show

extension :: SyntaxInfo -> [Maybe (Name, SynMatch)] -> [Syntax] -> IdrisParser PTerm
extension syn ns rules =
  choice $ flip map (groupBy (ruleGroup `on` syntaxSymbols) rules) $ \rs ->
    case head rs of -- can never be []
      Rule (symb:_) _ _ -> try $ do
        n <- extensionSymbol symb
        extension syn (n : ns) [Rule ss t ctx | (Rule (_:ss) t ctx) <- rs]
      -- If we have more than one Rule in this bucket, our grammar is
      -- nondeterministic.
      Rule [] ptm _ -> return (flatten (updateSynMatch (mapMaybe id ns) ptm))
  where
    ruleGroup [] [] = True
    ruleGroup (s1:_) (s2:_) = s1 == s2
    ruleGroup _ _ = False

    extensionSymbol :: SSymbol -> IdrisParser (Maybe (Name, SynMatch))
    extensionSymbol (Keyword n)    = do fc <- reservedFC (show n)
                                        highlightP fc AnnKeyword
                                        return Nothing
    extensionSymbol (Expr n)       = do tm <- expr syn
                                        return $ Just (n, SynTm tm)
    extensionSymbol (SimpleExpr n) = do tm <- simpleExpr syn
                                        return $ Just (n, SynTm tm)
    extensionSymbol (Binding n)    = do (b, fc) <- name
                                        return $ Just (n, SynBind fc b)
    extensionSymbol (Symbol s)     = do fc <- symbolFC s
                                        highlightP fc AnnKeyword
                                        return Nothing

    flatten :: PTerm -> PTerm -- flatten application
    flatten (PApp fc (PApp _ f as) bs) = flatten (PApp fc f (as ++ bs))
    flatten t = t

updateSynMatch = update
  where
    updateB :: [(Name, SynMatch)] -> (Name, FC) -> (Name, FC)
    updateB ns (n, fc) = case lookup n ns of
                           Just (SynBind tfc t) -> (t, tfc)
                           _ -> (n, fc)

    update :: [(Name, SynMatch)] -> PTerm -> PTerm
    update ns (PRef fc hls n) = case lookup n ns of
                                  Just (SynTm t) -> t
                                  _ -> PRef fc hls n
    update ns (PPatvar fc n) = uncurry (flip PPatvar) $ updateB ns (n, fc)
    update ns (PLam fc n nfc ty sc)
      = let (n', nfc') = updateB ns (n, nfc)
        in PLam fc n' nfc' (update ns ty) (update (dropn n ns) sc)
    update ns (PPi p n fc ty sc)
      = let (n', nfc') = updateB ns (n, fc)
        in PPi (updTacImp ns p) n' nfc'
               (update ns ty) (update (dropn n ns) sc)
    update ns (PLet fc n nfc ty val sc)
      = let (n', nfc') = updateB ns (n, nfc)
        in PLet fc n' nfc' (update ns ty)
                (update ns val) (update (dropn n ns) sc)
    update ns (PApp fc t args)
      = PApp fc (update ns t) (map (fmap (update ns)) args)
    update ns (PAppBind fc t args)
      = PAppBind fc (update ns t) (map (fmap (update ns)) args)
    update ns (PMatchApp fc n) = let (n', nfc') = updateB ns (n, fc)
                                 in PMatchApp nfc' n'
    update ns (PIfThenElse fc c t f)
      = PIfThenElse fc (update ns c) (update ns t) (update ns f)
    update ns (PCase fc c opts)
      = PCase fc (update ns c) (map (pmap (update ns)) opts)
    update ns (PRewrite fc by eq tm mty)
      = PRewrite fc by (update ns eq) (update ns tm) (fmap (update ns) mty)
    update ns (PPair fc hls p l r) = PPair fc hls p (update ns l) (update ns r)
    update ns (PDPair fc hls p l t r)
      = PDPair fc hls p (update ns l) (update ns t) (update ns r)
    update ns (PAs fc n t) = PAs fc (fst $ updateB ns (n, NoFC)) (update ns t)
    update ns (PAlternative ms a as) = PAlternative ms a (map (update ns) as)
    update ns (PHidden t) = PHidden (update ns t)
    update ns (PGoal fc r n sc) = PGoal fc (update ns r) n (update ns sc)
    update ns (PDoBlock ds) = PDoBlock $ map (upd ns) ds
      where upd :: [(Name, SynMatch)] -> PDo -> PDo
            upd ns (DoExp fc t) = DoExp fc (update ns t)
            upd ns (DoBind fc n nfc t) = DoBind fc n nfc (update ns t)
            upd ns (DoLet fc n nfc ty t) = DoLet fc n nfc (update ns ty) (update ns t)
            upd ns (DoBindP fc i t ts)
                    = DoBindP fc (update ns i) (update ns t)
                                 (map (\(l,r) -> (update ns l, update ns r)) ts)
            upd ns (DoLetP fc i t) = DoLetP fc (update ns i) (update ns t)
    update ns (PIdiom fc t) = PIdiom fc $ update ns t
    update ns (PMetavar fc n) = uncurry (flip PMetavar) $ updateB ns (n, fc)
    update ns (PProof tacs) = PProof $ map (updTactic ns) tacs
    update ns (PTactics tacs) = PTactics $ map (updTactic ns) tacs
    update ns (PDisamb nsps t) = PDisamb nsps $ update ns t
    update ns (PUnifyLog t) = PUnifyLog $ update ns t
    update ns (PNoImplicits t) = PNoImplicits $ update ns t
    update ns (PQuasiquote tm mty) = PQuasiquote (update ns tm) (fmap (update ns) mty)
    update ns (PUnquote t) = PUnquote $ update ns t
    update ns (PQuoteName n res fc) = let (n', fc') = (updateB ns (n, fc))
                                      in PQuoteName n' res fc'
    update ns (PRunElab fc t nsp) = PRunElab fc (update ns t) nsp
    update ns (PConstSugar fc t) = PConstSugar fc $ update ns t
    -- PConstSugar probably can't contain anything substitutable, but it's hard to track
    update ns t = t

    updTactic :: [(Name, SynMatch)] -> PTactic -> PTactic
    -- handle all the ones with Names explicitly, then use fmap for the rest with PTerms
    updTactic ns (Intro ns') = Intro $ map (fst . updateB ns . (, NoFC)) ns'
    updTactic ns (Focus n) = Focus . fst $ updateB ns (n, NoFC)
    updTactic ns (Refine n bs) = Refine (fst $ updateB ns (n, NoFC)) bs
    updTactic ns (Claim n t) = Claim (fst $ updateB ns (n, NoFC)) (update ns t)
    updTactic ns (MatchRefine n) = MatchRefine (fst $ updateB ns (n, NoFC))
    updTactic ns (LetTac n t) = LetTac (fst $ updateB ns (n, NoFC)) (update ns t)
    updTactic ns (LetTacTy n ty tm) = LetTacTy (fst $ updateB ns (n, NoFC)) (update ns ty) (update ns tm)
    updTactic ns (ProofSearch rec prover depth top psns hints) = ProofSearch rec prover depth
      (fmap (fst . updateB ns . (, NoFC)) top) (map (fst . updateB ns . (, NoFC)) psns) (map (fst . updateB ns . (, NoFC)) hints)
    updTactic ns (Try l r) = Try (updTactic ns l) (updTactic ns r)
    updTactic ns (TSeq l r) = TSeq (updTactic ns l) (updTactic ns r)
    updTactic ns (GoalType s tac) = GoalType s $ updTactic ns tac
    updTactic ns (TDocStr (Left n)) = TDocStr . Left . fst $ updateB ns (n, NoFC)
    updTactic ns t = fmap (update ns) t

    updTacImp ns (TacImp o st scr r) = TacImp o st (update ns scr) r
    updTacImp _  x                   = x

    dropn :: Name -> [(Name, a)] -> [(Name, a)]
    dropn n [] = []
    dropn n ((x,t) : xs) | n == x = xs
                         | otherwise = (x,t):dropn n xs


{- | Parses a (normal) built-in expression
@
InternalExpr ::=
    UnifyLog
  | RecordType
  | SimpleExpr
  | Lambda
  | QuoteGoal
  | Let
  | If
  | RewriteTerm
  | CaseExpr
  | DoBlock
  | App
  ;
@
-}
internalExpr :: SyntaxInfo -> IdrisParser PTerm
internalExpr syn =
         unifyLog syn
     <|> runElab syn
     <|> disamb syn
     <|> noImplicits syn
     <|> recordType syn
     <|> if_ syn
     <|> lambda syn
     <|> quoteGoal syn
     <|> let_ syn
     <|> rewriteTerm syn
     <|> doBlock syn
     <|> caseExpr syn
     <|> app syn
     <?> "expression"

{- | Parses the "impossible" keyword
@
Impossible ::= 'impossible'
@
-}
impossible :: IdrisParser PTerm
impossible = do fc <- reservedFC "impossible"
                highlightP fc AnnKeyword
                return PImpossible

{- | Parses a case expression
@
CaseExpr ::=
  'case' Expr 'of' OpenBlock CaseOption+ CloseBlock;
@
-}
caseExpr :: SyntaxInfo -> IdrisParser PTerm
caseExpr syn = do kw1 <- reservedFC "case"; fc <- getFC
                  scr <- expr syn; kw2 <- reservedFC "of";
                  opts <- indentedBlock1 (caseOption syn)
                  highlightP kw1 AnnKeyword
                  highlightP kw2 AnnKeyword
                  return (PCase fc scr opts)
               <?> "case expression"

{- | Parses a case in a case expression
@
CaseOption ::=
  Expr (Impossible | '=>' Expr) Terminator
  ;
@
-}
caseOption :: SyntaxInfo -> IdrisParser (PTerm, PTerm)
caseOption syn = do lhs <- expr (disallowImp (syn { inPattern = True }))
                    r <- impossible <|> symbol "=>" *> expr syn
                    return (lhs, r)
                 <?> "case option"

warnTacticDeprecation :: FC -> IdrisParser ()
warnTacticDeprecation fc =
 parserWarning fc (Just NoOldTacticDeprecationWarnings) (Msg "This style of tactic proof is deprecated. See %runElab for the replacement.")

{- | Parses a proof block
@
ProofExpr ::=
  'proof' OpenBlock Tactic'* CloseBlock
  ;
@
-}
proofExpr :: SyntaxInfo -> IdrisParser PTerm
proofExpr syn = do kw <- reservedFC "proof"
                   ts <- indentedBlock1 (tactic syn)
                   highlightP kw AnnKeyword
                   warnTacticDeprecation kw
                   return $ PProof ts
                <?> "proof block"

{- | Parses a tactics block
@
TacticsExpr :=
  'tactics' OpenBlock Tactic'* CloseBlock
;
@
-}
tacticsExpr :: SyntaxInfo -> IdrisParser PTerm
tacticsExpr syn = do kw <- reservedFC "tactics"
                     ts <- indentedBlock1 (tactic syn)
                     highlightP kw AnnKeyword
                     warnTacticDeprecation kw
                     return $ PTactics ts
                  <?> "tactics block"

{- | Parses a simple expression
@
SimpleExpr ::=
    {- External (User-defined) Simple Expression -}
  | '?' Name
  | % 'implementation'
  | 'Refl' ('{' Expr '}')?
  | ProofExpr
  | TacticsExpr
  | FnName
  | Idiom
  | List
  | Alt
  | Bracketed
  | Constant
  | Type
  | 'Void'
  | Quasiquote
  | NameQuote
  | Unquote
  | '_'
  ;
@
-}
simpleExpr :: SyntaxInfo -> IdrisParser PTerm
simpleExpr syn =
            try (simpleExternalExpr syn)
        <|> do (x, FC f (l, c) end) <- try (lchar '?' *> name)
               return (PMetavar (FC f (l, c-1) end) x)
        <|> do lchar '%'; fc <- getFC; reserved "implementation"; return (PResolveTC fc)
        <|> do lchar '%'; fc <- getFC; reserved "instance"
               parserWarning fc Nothing $ Msg "The use of %instance is deprecated, use %implementation instead."
               return (PResolveTC fc)
        <|> do reserved "elim_for"; fc <- getFC; t <- fst <$> fnName; return (PRef fc [] (SN $ ElimN t))
        <|> proofExpr syn
        <|> tacticsExpr syn
        <|> try (do fc <- reservedFC "Type*"; return $ PUniverse fc AllTypes)
        <|> do fc <- reservedFC "AnyType"; return $ PUniverse fc AllTypes
        <|> PType <$> reservedFC "Type"
        <|> do fc <- reservedFC "UniqueType"; return $ PUniverse fc UniqueType
        <|> do fc <- reservedFC "NullType"; return $ PUniverse fc NullType
        <|> do (c, cfc) <- constant
               fc <- getFC
               return (modifyConst syn fc (PConstant cfc c))
        <|> do symbol "'"; fc <- getFC; str <- fst <$> name
               return (PApp fc (PRef fc [] (sUN "Symbol_"))
                          [pexp (PConstant NoFC (Str (show str)))])
        <|> do (x, fc) <- fnName
               if inPattern syn
                  then option (PRef fc [fc] x)
                              (do reservedOp "@"
                                  s <- simpleExpr syn
                                  fcIn <- getFC
                                  return (PAs fcIn x s))
                  else return (PRef fc [fc] x)
        <|> idiom syn
        <|> listExpr syn
        <|> alt syn
        <|> do reservedOp "!"
               s <- simpleExpr syn
               fc <- getFC
               return (PAppBind fc s [])
        <|> bracketed (disallowImp syn)
        <|> quasiquote syn
        <|> namequote syn
        <|> unquote syn
        <|> do lchar '_'; return Placeholder
        <?> "expression"

{- |Parses an expression in parentheses
@
Bracketed ::= '(' Bracketed'
@
 -}
bracketed :: SyntaxInfo -> IdrisParser PTerm
bracketed syn = do (FC fn (sl, sc) _) <- getFC
                   lchar '(' <?> "parenthesized expression"
                   bracketed' (FC fn (sl, sc) (sl, sc+1)) (syn { withAppAllowed = True })

{- |Parses the rest of an expression in braces
@
Bracketed' ::=
  ')'
  | Expr ')'
  | ExprList ')'
  | DependentPair ')'
  | Operator Expr ')'
  | Expr Operator ')'
  ;
@
-}
bracketed' :: FC -> SyntaxInfo -> IdrisParser PTerm
bracketed' open syn =
            do (FC f start (l, c)) <- getFC
               lchar ')'
               return $ PTrue (spanFC open (FC f start (l, c+1))) TypeOrTerm
        <|> try (dependentPair TypeOrTerm [] open syn)
        <|> try (do fc <- getFC; o <- operator; e <- expr syn; lchar ')'
                    -- No prefix operators! (bit of a hack here...)
                    if (o == "-" || o == "!")
                      then fail "minus not allowed in section"
                      else return $ PLam fc (sMN 1000 "ARG") NoFC Placeholder
                         (PApp fc (PRef fc [] (sUN o)) [pexp (PRef fc [] (sMN 1000 "ARG")),
                                                        pexp e]))
        <|> try (do l <- simpleExpr syn
                    op <- option Nothing (do o <- operator
                                             lchar ')'
                                             return (Just o))
                    fc0 <- getFC
                    case op of
                         Nothing -> bracketedExpr syn open l
                         Just o -> return $ PLam fc0 (sMN 1000 "ARG") NoFC Placeholder
                             (PApp fc0 (PRef fc0 [] (sUN o)) [pexp l,
                                                              pexp (PRef fc0 [] (sMN 1000 "ARG"))]))
        <|> do l <- expr (allowConstr syn)
               bracketedExpr (allowConstr syn) open l



{-| Parses the rest of a dependent pair after '(' or '(Expr **' -}
dependentPair :: PunInfo -> [(PTerm, Maybe (FC, PTerm), FC)] -> FC -> SyntaxInfo -> IdrisParser PTerm
dependentPair pun prev openFC syn =
  if null prev then
      nametypePart <|> namePart
  else
    case pun of
      IsType -> nametypePart <|> namePart <|> exprPart True
      IsTerm -> exprPart False
      TypeOrTerm -> nametypePart <|> namePart <|> exprPart False
  where nametypePart = do
          (ln, lnfc, colonFC) <- try $ do
            (ln, lnfc) <- name
            colonFC <- lcharFC ':'
            return (ln, lnfc, colonFC)
          lty <- expr' syn
          starsFC <- reservedOpFC "**"
          dependentPair IsType ((PRef lnfc [] ln, Just (colonFC, lty), starsFC):prev) openFC syn
        namePart = try $ do
          (ln, lnfc) <- name
          starsFC <- reservedOpFC "**"
          dependentPair pun ((PRef lnfc [] ln, Nothing, starsFC):prev) openFC syn
        exprPart isEnd = do
          e <- expr syn
          sepFCE <-
            let stars = (Left <$> reservedOpFC "**")
                ending = (Right <$> lcharFC ')')
            in if isEnd then ending else stars <|> ending
          case sepFCE of
            Left starsFC -> dependentPair IsTerm ((e, Nothing, starsFC):prev) openFC syn
            Right closeFC ->
              return (mkPDPairs pun openFC closeFC (reverse prev) e)
        mkPDPairs pun openFC closeFC ((e, cfclty, starsFC):bnds) r =
              (PDPair openFC ([openFC] ++ maybe [] ((: []) . fst) cfclty ++ [starsFC, closeFC] ++ (=<<) (\(_,cfclty,sfc) -> maybe [] ((: []) . fst) cfclty ++ [sfc]) bnds)
                               pun e (maybe Placeholder snd cfclty) (mergePDPairs pun starsFC bnds r))
        mergePDPairs pun starsFC' [] r = r
        mergePDPairs pun starsFC' ((e, cfclty, starsFC):bnds) r =
           PDPair starsFC' [] pun e (maybe Placeholder snd cfclty) (mergePDPairs pun starsFC bnds r)

-- | Parse the contents of parentheses, after an expression has been parsed.
bracketedExpr :: SyntaxInfo -> FC -> PTerm -> IdrisParser PTerm
bracketedExpr syn openParenFC e =
             do lchar ')'; return e
        <|>  do exprs <- some (do comma <- lcharFC ','
                                  r <- expr syn
                                  return (r, comma))
                closeParenFC <- lcharFC ')'
                let hilite = [openParenFC, closeParenFC] ++ map snd exprs
                return $ PPair openParenFC hilite TypeOrTerm e (mergePairs exprs)
        <|>  do starsFC <- reservedOpFC "**"
                dependentPair IsTerm [(e, Nothing, starsFC)] openParenFC syn
        <?> "end of bracketed expression"
  where mergePairs :: [(PTerm, FC)] -> PTerm
        mergePairs [(t, fc)]    = t
        mergePairs ((t, fc):rs) = PPair fc [] TypeOrTerm t (mergePairs rs)

-- bit of a hack here. If the integer doesn't fit in an Int, treat it as a
-- big integer, otherwise try fromInteger and the constants as alternatives.
-- a better solution would be to fix fromInteger to work with Integer, as the
-- name suggests, rather than Int
{-| Finds optimal type for integer constant -}
modifyConst :: SyntaxInfo -> FC -> PTerm -> PTerm
modifyConst syn fc (PConstant inFC (BI x))
    | not (inPattern syn)
        = PConstSugar inFC $ -- wrap in original location for highlighting
            PAlternative [] FirstSuccess
              (PApp fc (PRef fc [] (sUN "fromInteger")) [pexp (PConstant NoFC (BI (fromInteger x)))]
              : consts)
    | otherwise = PConstSugar inFC $
                    PAlternative [] FirstSuccess consts
    where
      consts = [ PConstant inFC (BI x)
               , PConstant inFC (I (fromInteger x))
               , PConstant inFC (B8 (fromInteger x))
               , PConstant inFC (B16 (fromInteger x))
               , PConstant inFC (B32 (fromInteger x))
               , PConstant inFC (B64 (fromInteger x))
               ]
modifyConst syn fc x = x

{- | Parses an alternative expression
@
  Alt ::= '(|' Expr_List '|)';

  Expr_List ::=
    Expr'
    | Expr' ',' Expr_List
  ;
@
-}
alt :: SyntaxInfo -> IdrisParser PTerm
alt syn = do symbol "(|"; alts <- sepBy1 (expr' (syn { withAppAllowed = False })) (lchar ','); symbol "|)"
             return (PAlternative [] FirstSuccess alts)

{- | Parses a possibly hidden simple expression
@
HSimpleExpr ::=
  '.' SimpleExpr
  | SimpleExpr
  ;
@
-}
hsimpleExpr :: SyntaxInfo -> IdrisParser PTerm
hsimpleExpr syn =
  do lchar '.'
     e <- simpleExpr syn
     return $ PHidden e
  <|> simpleExpr syn
  <?> "expression"

{- | Parses a unification log expression
UnifyLog ::=
  '%' 'unifyLog' SimpleExpr
  ;
-}
unifyLog :: SyntaxInfo -> IdrisParser PTerm
unifyLog syn = do (FC fn (sl, sc) kwEnd) <- try (lchar '%' *> reservedFC "unifyLog")
                  tm <- simpleExpr syn
                  highlightP (FC fn (sl, sc-1) kwEnd) AnnKeyword
                  return (PUnifyLog tm)
               <?> "unification log expression"

{- | Parses a new-style tactics expression
RunTactics ::=
  '%' 'runElab' SimpleExpr
  ;
-}
runElab :: SyntaxInfo -> IdrisParser PTerm
runElab syn = do (FC fn (sl, sc) kwEnd) <- try (lchar '%' *> reservedFC "runElab")
                 fc <- getFC
                 tm <- simpleExpr syn
                 highlightP (FC fn (sl, sc-1) kwEnd) AnnKeyword
                 return $ PRunElab fc tm (syn_namespace syn)
              <?> "new-style tactics expression"

{- | Parses a disambiguation expression
Disamb ::=
  'with' NameList Expr
  ;
-}
disamb :: SyntaxInfo -> IdrisParser PTerm
disamb syn = do kw <- reservedFC "with"
                ns <- sepBy1 (fst <$> name) (lchar ',')
                tm <- expr' syn
                highlightP kw AnnKeyword
                return (PDisamb (map tons ns) tm)
               <?> "namespace disambiguation expression"
  where tons (NS n s) = txt (show n) : s
        tons n = [txt (show n)]
{- | Parses a no implicits expression
@
NoImplicits ::=
  '%' 'noImplicits' SimpleExpr
  ;
@
-}
noImplicits :: SyntaxInfo -> IdrisParser PTerm
noImplicits syn = do try (lchar '%' *> reserved "noImplicits")
                     tm <- simpleExpr syn
                     return (PNoImplicits tm)
                 <?> "no implicits expression"

{- | Parses a function application expression
@
App ::=
  'mkForeign' Arg Arg*
  | MatchApp
  | SimpleExpr Arg*
  ;
MatchApp ::=
  SimpleExpr '<==' FnName
  ;
@
-}
app :: SyntaxInfo -> IdrisParser PTerm
app syn = do f <- simpleExpr syn
             (do try $ reservedOp "<=="
                 fc <- getFC
                 ff <- fst <$> fnName
                 return (PLet fc (sMN 0 "match") NoFC
                               f
                               (PMatchApp fc ff)
                               (PRef fc [] (sMN 0 "match")))
                   <?> "matching application expression") <|>
               (do fc <- getFC
                   i <- get
                   args <- many (do notEndApp; arg syn)
                   wargs <- if withAppAllowed syn && not (inPattern syn)
                              then many (do notEndApp; reservedOp "|"; expr' syn)
                              else return []
                   case args of
                     [] -> return f
                     _  -> return (withApp fc (flattenFromInt fc f args) wargs))
       <?> "function application"
   where
    -- bit of a hack to deal with the situation where we're applying a
    -- literal to an argument, which we may want for obscure applications
    -- of fromInteger, and this will help disambiguate better.
    -- We know, at least, it won't be one of the constants!
    flattenFromInt fc (PAlternative _ x alts) args
      | Just i <- getFromInt alts
           = PApp fc (PRef fc [] (sUN "fromInteger")) (i : args)
    flattenFromInt fc f args = PApp fc f args

    withApp fc tm [] = tm
    withApp fc tm (a : as) = withApp fc (PWithApp fc tm a) as

    getFromInt ((PApp _ (PRef _ _ n) [a]) : _) | n == sUN "fromInteger" = Just a
    getFromInt (_ : xs) = getFromInt xs
    getFromInt _ = Nothing

{-| Parses a function argument
@
Arg ::=
  ImplicitArg
  | ConstraintArg
  | SimpleExpr
  ;
@
-}
arg :: SyntaxInfo -> IdrisParser PArg
arg syn =  implicitArg syn
       <|> constraintArg syn
       <|> do e <- simpleExpr syn
              return (pexp e)
       <?> "function argument"

{-| Parses an implicit function argument
@
ImplicitArg ::=
  '{' Name ('=' Expr)? '}'
  ;
@
-}
implicitArg :: SyntaxInfo -> IdrisParser PArg
implicitArg syn = do lchar '{'
                     (n, nfc) <- name
                     fc <- getFC
                     v <- option (PRef nfc [nfc] n) (do lchar '='
                                                        expr syn)
                     lchar '}'
                     return (pimp n v True)
                  <?> "implicit function argument"

{-| Parses a constraint argument (for selecting a named interface implementation)

>    ConstraintArg ::=
>      '@{' Expr '}'
>      ;

-}
constraintArg :: SyntaxInfo -> IdrisParser PArg
constraintArg syn = do symbol "@{"
                       e <- expr syn
                       symbol "}"
                       return (pconst e)
                    <?> "constraint argument"

{-| Parses a quasiquote expression (for building reflected terms using the elaborator)

> Quasiquote ::= '`(' Expr ')'

-}
quasiquote :: SyntaxInfo -> IdrisParser PTerm
quasiquote syn = do startFC <- symbolFC "`("
                    e <- expr syn { syn_in_quasiquote = (syn_in_quasiquote syn) + 1 ,
                                    inPattern = False }
                    g <- optional $
                           do fc <- symbolFC ":"
                              ty <- expr syn { inPattern = False } -- don't allow antiquotes
                              return (ty, fc)
                    endFC <- symbolFC ")"
                    mapM_ (uncurry highlightP) [(startFC, AnnKeyword), (endFC, AnnKeyword), (spanFC startFC endFC, AnnQuasiquote)]
                    case g of
                      Just (_, fc) -> highlightP fc AnnKeyword
                      _ -> return ()
                    return $ PQuasiquote e (fst <$> g)
                 <?> "quasiquotation"

{-| Parses an unquoting inside a quasiquotation (for building reflected terms using the elaborator)

> Unquote ::= ',' Expr

-}
unquote :: SyntaxInfo -> IdrisParser PTerm
unquote syn = do guard (syn_in_quasiquote syn > 0)
                 startFC <- symbolFC "~"
                 e <- simpleExpr syn { syn_in_quasiquote = syn_in_quasiquote syn - 1 }
                 endFC <- getFC
                 highlightP startFC AnnKeyword
                 highlightP (spanFC startFC endFC) AnnAntiquote
                 return $ PUnquote e
              <?> "unquotation"

{-| Parses a quotation of a name (for using the elaborator to resolve boring details)

> NameQuote ::= '`{' Name '}'

-}
namequote :: SyntaxInfo -> IdrisParser PTerm
namequote syn = do (startFC, res) <-
                     try (do fc <- symbolFC "`{{"
                             return (fc, False)) <|>
                       (do fc <- symbolFC "`{"
                           return (fc, True))
                   (n, nfc) <- fnName
                   endFC <- if res then symbolFC "}" else symbolFC "}}"
                   mapM_ (uncurry highlightP)
                         [ (startFC, AnnKeyword)
                         , (endFC, AnnKeyword)
                         , (spanFC startFC endFC, AnnQuasiquote)
                         ]
                   return $ PQuoteName n res nfc
                <?> "quoted name"


{-| Parses a record field setter expression
@
RecordType ::=
  'record' '{' FieldTypeList '}';
@
@
FieldTypeList ::=
  FieldType
  | FieldType ',' FieldTypeList
  ;
@
@
FieldType ::=
  FnName '=' Expr
  ;
@
-}

data SetOrUpdate = FieldSet PTerm | FieldUpdate PTerm

recordType :: SyntaxInfo -> IdrisParser PTerm
recordType syn =
      do kw <- reservedFC "record"
         lchar '{'
         fgs <- fieldGetOrSet
         lchar '}'
         fc <- getFC
         rec <- optional (do notEndApp; simpleExpr syn)
         highlightP kw AnnKeyword
         case fgs of
              Left fields ->
                case rec of
                   Nothing ->
                       return (PLam fc (sMN 0 "fldx") NoFC Placeholder
                                   (applyAll fc fields (PRef fc [] (sMN 0 "fldx"))))
                   Just v -> return (applyAll fc fields v)
              Right fields ->
                case rec of
                   Nothing ->
                       return (PLam fc (sMN 0 "fldx") NoFC Placeholder
                                 (getAll fc (reverse fields)
                                     (PRef fc [] (sMN 0 "fldx"))))
                   Just v -> return (getAll fc (reverse fields) v)

       <?> "record setting expression"
   where fieldSet :: IdrisParser ([Name], SetOrUpdate)
         fieldSet = do ns <- fieldGet
                       (do lchar '='
                           e <- expr syn
                           return (ns, FieldSet e))
                         <|> do symbol "$="
                                e <- expr syn
                                return (ns, FieldUpdate e)
                    <?> "field setter"

         fieldGet :: IdrisParser [Name]
         fieldGet = sepBy1 (fst <$> fnName) (symbol "->")

         fieldGetOrSet :: IdrisParser (Either [([Name], SetOrUpdate)] [Name])
         fieldGetOrSet = try (do fs <- sepBy1 fieldSet (lchar ',')
                                 return (Left fs))
                     <|> do f <- fieldGet
                            return (Right f)

         applyAll :: FC -> [([Name], SetOrUpdate)] -> PTerm -> PTerm
         applyAll fc [] x = x
         applyAll fc ((ns, e) : es) x
            = applyAll fc es (doUpdate fc ns e x)

         doUpdate fc ns (FieldUpdate e) get
              = let get' = getAll fc (reverse ns) get in
                    doUpdate fc ns (FieldSet (PApp fc e [pexp get'])) get
         doUpdate fc [n] (FieldSet e) get
              = PApp fc (PRef fc [] (mkType n)) [pexp e, pexp get]
         doUpdate fc (n : ns) e get
              = PApp fc (PRef fc [] (mkType n))
                  [pexp (doUpdate fc ns e (PApp fc (PRef fc [] n) [pexp get])),
                   pexp get]

         getAll :: FC -> [Name] -> PTerm -> PTerm
         getAll fc [n] e = PApp fc (PRef fc [] n) [pexp e]
         getAll fc (n:ns) e = PApp fc (PRef fc [] n) [pexp (getAll fc ns e)]


-- | Creates setters for record types on necessary functions
mkType :: Name -> Name
mkType (UN n) = sUN ("set_" ++ str n)
mkType (MN 0 n) = sMN 0 ("set_" ++ str n)
mkType (NS n s) = NS (mkType n) s

{- | Parses a type signature
@
TypeSig ::=
  ':' Expr
  ;
@
@
TypeExpr ::= ConstraintList? Expr;
@
 -}
typeExpr :: SyntaxInfo -> IdrisParser PTerm
typeExpr syn = do cs <- if implicitAllowed syn then constraintList syn else return []
                  sc <- expr (allowConstr syn)
                  return (bindList (\r -> PPi (constraint { pcount = r })) cs sc)
               <?> "type signature"

{- | Parses a lambda expression
@
Lambda ::=
    '\\' TypeOptDeclList LambdaTail
  | '\\' SimpleExprList  LambdaTail
  ;
@
@
SimpleExprList ::=
  SimpleExpr
  | SimpleExpr ',' SimpleExprList
  ;
@
@
LambdaTail ::=
    Impossible
  | '=>' Expr
@
-}
lambda :: SyntaxInfo -> IdrisParser PTerm
lambda syn = do lchar '\\' <?> "lambda expression"
                ((do xt <- try $ tyOptDeclList (disallowImp syn)
                     fc <- getFC
                     sc <- lambdaTail
                     return (bindList (\r -> PLam fc) xt sc))
                 <|>
                 (do ps <- sepBy (do fc <- getFC
                                     e <- simpleExpr (disallowImp (syn { inPattern = True }))
                                     return (fc, e))
                                 (lchar ',')
                     sc <- lambdaTail
                     return (pmList (zip [0..] ps) sc)))
                  <?> "lambda expression"
    where pmList :: [(Int, (FC, PTerm))] -> PTerm -> PTerm
          pmList [] sc = sc
          pmList ((i, (fc, x)) : xs) sc
                = PLam fc (sMN i "lamp") NoFC Placeholder
                        (PCase fc (PRef fc [] (sMN i "lamp"))
                                [(x, pmList xs sc)])
          lambdaTail :: IdrisParser PTerm
          lambdaTail = impossible <|> symbol "=>" *> expr syn

{- | Parses a term rewrite expression
@
RewriteTerm ::=
  'rewrite' Expr ('==>' Expr)? 'in' Expr
  ;
@
-}
rewriteTerm :: SyntaxInfo -> IdrisParser PTerm
rewriteTerm syn = do kw <- reservedFC "rewrite"
                     fc <- getFC
                     prf <- expr syn
                     giving <- optional (do symbol "==>"; expr' syn)
                     using <- optional (do reserved "using"
                                           (n, _) <- name
                                           return n)
                     kw' <- reservedFC "in";  sc <- expr syn
                     highlightP kw AnnKeyword
                     highlightP kw' AnnKeyword
                     return (PRewrite fc using prf sc giving)
                  <?> "term rewrite expression"

{- |Parses a let binding
@
Let ::=
  'let' Name TypeSig'? '=' Expr  'in' Expr
| 'let' Expr'          '=' Expr' 'in' Expr

TypeSig' ::=
  ':' Expr'
  ;
@
 -}
let_ :: SyntaxInfo -> IdrisParser PTerm
let_ syn = try (do kw <- reservedFC "let"
                   ls <- indentedBlock (let_binding syn)
                   kw' <- reservedFC "in";  sc <- expr syn
                   highlightP kw AnnKeyword; highlightP kw' AnnKeyword
                   return (buildLets ls sc))
           <?> "let binding"
  where buildLets [] sc = sc
        buildLets ((fc, PRef nfc _ n, ty, v, []) : ls) sc
          = PLet fc n nfc ty v (buildLets ls sc)
        buildLets ((fc, pat, ty, v, alts) : ls) sc
          = PCase fc v ((pat, buildLets ls sc) : alts)

let_binding syn = do fc <- getFC;
                     pat <- expr' (syn { inPattern = True })
                     ty <- option Placeholder (do lchar ':'; expr' syn)
                     lchar '='
                     v <- expr (syn { withAppAllowed = isVar pat })
                     ts <- option [] (do lchar '|'
                                         sepBy1 (do_alt syn) (lchar '|'))
                     return (fc,pat,ty,v,ts)
   where isVar (PRef _ _ _) = True
         isVar _ = False

{- | Parses a conditional expression
@
If ::= 'if' Expr 'then' Expr 'else' Expr
@

-}
if_ :: SyntaxInfo -> IdrisParser PTerm
if_ syn = (do ifFC <- reservedFC "if"
              fc <- getFC
              c <- expr syn
              thenFC <- reservedFC "then"
              t <- expr syn
              elseFC <- reservedFC "else"
              f <- expr syn
              mapM_ (flip highlightP AnnKeyword) [ifFC, thenFC, elseFC]
              return (PIfThenElse fc c t f))
          <?> "conditional expression"


{- | Parses a quote goal

@
QuoteGoal ::=
  'quoteGoal' Name 'by' Expr 'in' Expr
  ;
@
 -}
quoteGoal :: SyntaxInfo -> IdrisParser PTerm
quoteGoal syn = do kw1 <- reservedFC "quoteGoal"; n <- fst <$> name;
                   kw2 <- reservedFC "by"
                   r <- expr syn
                   kw3 <- reservedFC "in"
                   fc <- getFC
                   sc <- expr syn
                   mapM_ (flip highlightP AnnKeyword) [kw1, kw2, kw3]
                   return (PGoal fc r n sc)
                <?> "quote goal expression"

{- | Parses a dependent type signature

@
Pi ::= PiOpts Static? Pi'
@

@
Pi' ::=
    OpExpr ('->' Pi)?
  | '(' TypeDeclList           ')'            '->' Pi
  | '{' TypeDeclList           '}'            '->' Pi
  | '{' 'auto'    TypeDeclList '}'            '->' Pi
  | '{' 'default' SimpleExpr TypeDeclList '}' '->' Pi
  ;
@
 -}

bindsymbol opts st syn
     = do symbol "->"
          return (Exp opts st False RigW)

explicitPi opts st syn
   = do xt <- try (lchar '(' *> typeDeclList syn <* lchar ')')
        binder <- bindsymbol opts st syn
        sc <- expr (allowConstr syn)
        return (bindList (\r -> PPi (binder { pcount = r })) xt sc)

autoImplicit opts st syn
   = do kw <- reservedFC "auto"
        when (st == Static) $ fail "auto implicits can not be static"
        xt <- typeDeclList syn
        lchar '}'
        symbol "->"
        sc <- expr (allowConstr syn)
        highlightP kw AnnKeyword
        return (bindList (\r -> PPi
          (TacImp [] Dynamic (PTactics [ProofSearch True True 100 Nothing [] []]) r)) xt sc)

defaultImplicit opts st syn = do
   kw <- reservedFC "default"
   when (st == Static) $ fail "default implicits can not be static"
   ist <- get
   script' <- simpleExpr syn
   let script = debindApp syn . desugar syn ist $ script'
   xt <- typeDeclList syn
   lchar '}'
   symbol "->"
   sc <- expr (allowConstr syn)
   highlightP kw AnnKeyword
   return (bindList (\r -> PPi (TacImp [] Dynamic script r)) xt sc)

normalImplicit opts st syn = do
   xt <- typeDeclList syn <* lchar '}'
   symbol "->"
   cs <- constraintList syn
   sc <- expr syn
   let (im,cl)
          = if implicitAllowed syn
               then (Imp opts st False (Just (Impl False True False)) True RigW,
                      constraint)
               else (Imp opts st False (Just (Impl False False False)) True RigW,
                     Imp opts st False (Just (Impl True False False)) True RigW)
   return (bindList (\r -> PPi (im { pcount = r })) xt
           (bindList (\r -> PPi (cl { pcount = r })) cs sc))

constraintPi opts st syn =
   do cs <- constraintList1 syn
      sc <- expr syn
      if implicitAllowed syn
         then return (bindList (\r -> PPi constraint { pcount = r }) cs sc)
         else return (bindList (\r -> PPi (Imp opts st False (Just (Impl True False False)) True r))
                               cs sc)

implicitPi opts st syn =
      autoImplicit opts st syn
        <|> defaultImplicit opts st syn
          <|> normalImplicit opts st syn

unboundPi opts st syn = do
       x <- opExpr syn
       (do binder <- bindsymbol opts st syn
           sc <- expr syn
           return (PPi binder (sUN "__pi_arg") NoFC x sc))
              <|> return x

-- This is used when we need to disambiguate from a constraint list
unboundPiNoConstraint opts st syn = do
       x <- opExpr syn
       (do binder <- bindsymbol opts st syn
           sc <- expr syn
           notFollowedBy $ reservedOp "=>"
           return (PPi binder (sUN "__pi_arg") NoFC x sc))
              <|> do notFollowedBy $ reservedOp "=>"
                     return x


pi :: SyntaxInfo -> IdrisParser PTerm
pi syn =
     do opts <- piOpts syn
        st   <- static
        explicitPi opts st syn
         <|> try (do lchar '{'; implicitPi opts st syn)
         <|> if constraintAllowed syn
                then try (unboundPiNoConstraint opts st syn)
                         <|> constraintPi opts st syn
                else unboundPi opts st syn
  <?> "dependent type signature"

{- | Parses Possible Options for Pi Expressions
@
  PiOpts ::= '.'?
@
-}
piOpts :: SyntaxInfo -> IdrisParser [ArgOpt]
piOpts syn | implicitAllowed syn =
        lchar '.' *> return [InaccessibleArg]
    <|> return []
piOpts syn = return []

{- | Parses a type constraint list

@
ConstraintList ::=
    '(' Expr_List ')' '=>'
  | Expr              '=>'
  ;
@
-}
constraintList :: SyntaxInfo -> IdrisParser [(RigCount, Name, FC, PTerm)]
constraintList syn = try (constraintList1 syn)
                     <|> return []

constraintList1 :: SyntaxInfo -> IdrisParser [(RigCount, Name, FC, PTerm)]
constraintList1 syn = try (do lchar '('
                              tys <- sepBy1 nexpr (lchar ',')
                              lchar ')'
                              reservedOp "=>"
                              return tys)
                  <|> try (do t <- opExpr (disallowImp syn)
                              reservedOp "=>"
                              return [(RigW, defname, NoFC, t)])
                  <?> "type constraint list"
  where nexpr = try (do (n, fc) <- name; lchar ':'
                        e <- expr (disallowImp syn)
                        return (RigW, n, fc, e))
                <|> do e <- expr (disallowImp syn)
                       return (RigW, defname, NoFC, e)
        defname = sMN 0 "constraint"

{- | Parses a type declaration list
@
TypeDeclList ::=
    FunctionSignatureList
  | NameList TypeSig
  ;
@

@
FunctionSignatureList ::=
    Name TypeSig
  | Name TypeSig ',' FunctionSignatureList
  ;
@
-}
typeDeclList :: SyntaxInfo -> IdrisParser [(RigCount, Name, FC, PTerm)]
typeDeclList syn = try (sepBy1 (do rig <- option RigW rigCount
                                   (x, xfc) <- fnName
                                   lchar ':'
                                   t <- typeExpr (disallowImp syn)
                                   return (rig, x, xfc, t))
                           (lchar ','))
                   <|> do ns <- sepBy1 name (lchar ',')
                          lchar ':'
                          t <- typeExpr (disallowImp syn)
                          return (map (\(x, xfc) -> (RigW, x, xfc, t)) ns)
                   <?> "type declaration list"
  where
    rigCount = do lchar '1'; return Rig1
           <|> do lchar '0'; return Rig0

{- | Parses a type declaration list with optional parameters
@
TypeOptDeclList ::=
    NameOrPlaceholder TypeSig?
  | NameOrPlaceholder TypeSig? ',' TypeOptDeclList
  ;
@

@
NameOrPlaceHolder ::= Name | '_';
@
-}
tyOptDeclList :: SyntaxInfo -> IdrisParser [(RigCount, Name, FC, PTerm)]
tyOptDeclList syn = sepBy1 (do (x, fc) <- nameOrPlaceholder
                               t <- option Placeholder (do lchar ':'
                                                           expr syn)
                               return (RigW, x, fc, t))
                           (lchar ',')
                    <?> "type declaration list"
    where  nameOrPlaceholder :: IdrisParser (Name, FC)
           nameOrPlaceholder = fnName
                           <|> do symbol "_"
                                  return (sMN 0 "underscore", NoFC)
                           <?> "name or placeholder"

{- | Parses a list literal expression e.g. [1,2,3] or a comprehension [ (x, y) | x <- xs , y <- ys ]
@
ListExpr ::=
     '[' ']'
  | '[' Expr '|' DoList ']'
  | '[' ExprList ']'
;
@
@
DoList ::=
    Do
  | Do ',' DoList
  ;
@
@
ExprList ::=
  Expr
  | Expr ',' ExprList
  ;
@
 -}
listExpr :: SyntaxInfo -> IdrisParser PTerm
listExpr syn = do (FC f (l, c) _) <- getFC
                  lchar '['; fc <- getFC;
                  (try . token $ do (char ']' <?> "end of list expression")
                                    (FC _ _ (l', c')) <- getFC
                                    return (mkNil (FC f (l, c) (l', c'))))
                   <|> (do x <- expr (syn { withAppAllowed = False }) <?> "expression"
                           (do try (lchar '|') <?> "list comprehension"
                               qs <- sepBy1 (do_ syn) (lchar ',')
                               lchar ']'
                               return (PDoBlock (map addGuard qs ++
                                          [DoExp fc (PApp fc (PRef fc [] (sUN "pure"))
                                                       [pexp x])]))) <|>
                            (do xs <- many (do (FC fn (sl, sc) _) <- getFC
                                               lchar ',' <?> "list element"
                                               let commaFC = FC fn (sl, sc) (sl, sc + 1)
                                               elt <- expr syn
                                               return (elt, commaFC))
                                (FC fn (sl, sc) _) <- getFC
                                lchar ']' <?> "end of list expression"
                                let rbrackFC = FC fn (sl, sc) (sl, sc+1)
                                return (mkList fc rbrackFC ((x, (FC f (l, c) (l, c+1))) : xs))))
                <?> "list expression"
  where
    mkNil :: FC -> PTerm
    mkNil fc = PRef fc [fc] (sUN "Nil")
    mkList :: FC -> FC -> [(PTerm, FC)] -> PTerm
    mkList errFC nilFC [] = PRef nilFC [nilFC] (sUN "Nil")
    mkList errFC nilFC ((x, fc) : xs) = PApp errFC (PRef fc [fc] (sUN "::")) [pexp x, pexp (mkList errFC nilFC xs)]
    addGuard :: PDo -> PDo
    addGuard (DoExp fc e) = DoExp fc (PApp fc (PRef fc [] (sUN "guard"))
                                              [pexp e])
    addGuard x = x

{- | Parses a do-block
@
Do' ::= Do KeepTerminator;
@

@
DoBlock ::=
  'do' OpenBlock Do'+ CloseBlock
  ;
@
 -}
doBlock :: SyntaxInfo -> IdrisParser PTerm
doBlock syn
    = do kw <- reservedFC "do"
         ds <- indentedBlock1 (do_ syn)
         highlightP kw AnnKeyword
         return (PDoBlock ds)
      <?> "do block"

{- | Parses an expression inside a do block
@
Do ::=
    'let' Name  TypeSig'?      '=' Expr
  | 'let' Expr'                '=' Expr
  | Name  '<-' Expr
  | Expr' '<-' Expr
  | Expr
  ;
@
-}
do_ :: SyntaxInfo -> IdrisParser PDo
do_ syn
     = try (do kw <- reservedFC "let"
               (i, ifc) <- name
               ty <- option Placeholder (do lchar ':'
                                            expr' syn)
               reservedOp "="
               fc <- getFC
               e <- expr syn
               highlightP kw AnnKeyword
               return (DoLet fc i ifc ty e))
   <|> try (do kw <- reservedFC "let"
               i <- expr' syn
               reservedOp "="
               fc <- getFC
               sc <- expr syn
               highlightP kw AnnKeyword
               return (DoLetP fc i sc))
   <|> try (do (i, ifc) <- name
               symbol "<-"
               fc <- getFC
               e <- expr (syn { withAppAllowed = False });
               option (DoBind fc i ifc e)
                      (do lchar '|'
                          ts <- sepBy1 (do_alt (syn { withAppAllowed = False })) (lchar '|')
                          return (DoBindP fc (PRef ifc [ifc] i) e ts)))
   <|> try (do i <- expr' syn
               symbol "<-"
               fc <- getFC
               e <- expr (syn { withAppAllowed = False });
               option (DoBindP fc i e [])
                      (do lchar '|'
                          ts <- sepBy1 (do_alt (syn { withAppAllowed = False })) (lchar '|')
                          return (DoBindP fc i e ts)))
   <|> do e <- expr syn
          fc <- getFC
          return (DoExp fc e)
   <?> "do block expression"

do_alt syn = do l <- expr' syn
                option (Placeholder, l)
                       (do symbol "=>"
                           r <- expr' syn
                           return (l, r))

{- | Parses an expression in idiom brackets
@
Idiom ::= '[|' Expr '|]';
@
-}
idiom :: SyntaxInfo -> IdrisParser PTerm
idiom syn
    = do symbol "[|"
         fc <- getFC
         e <- expr (syn { withAppAllowed = False })
         symbol "|]"
         return (PIdiom fc e)
      <?> "expression in idiom brackets"

{- |Parses a constant or literal expression

@
Constant ::=
    'Integer'
  | 'Int'
  | 'Char'
  | 'Double'
  | 'String'
  | 'Bits8'
  | 'Bits16'
  | 'Bits32'
  | 'Bits64'
  | Float_t
  | Natural_t
  | VerbatimString_t
  | String_t
  | Char_t
  ;
@
-}

constants :: [(String, Idris.Core.TT.Const)]
constants =
  [ ("Integer",            AType (ATInt ITBig))
  , ("Int",                AType (ATInt ITNative))
  , ("Char",               AType (ATInt ITChar))
  , ("Double",             AType ATFloat)
  , ("String",             StrType)
  , ("prim__WorldType",    WorldType)
  , ("prim__TheWorld",     TheWorld)
  , ("Bits8",              AType (ATInt (ITFixed IT8)))
  , ("Bits16",             AType (ATInt (ITFixed IT16)))
  , ("Bits32",             AType (ATInt (ITFixed IT32)))
  , ("Bits64",             AType (ATInt (ITFixed IT64)))
  ]

-- | Parse a constant and its source span
constant :: IdrisParser (Idris.Core.TT.Const, FC)
constant = choice [ do fc <- reservedFC name; return (ty, fc)
                  | (name, ty) <- constants
                  ]
        <|> do (f, fc) <- try float; return (Fl f, fc)
        <|> do (i, fc) <- natural; return (BI i, fc)
        <|> do (s, fc) <- verbatimStringLiteral; return (Str s, fc)
        <|> do (s, fc) <- stringLiteral;  return (Str s, fc)
        <|> do (c, fc) <- try charLiteral; return (Ch c, fc) --Currently ambigous with symbols
        <?> "constant or literal"

{- | Parses a verbatim multi-line string literal (triple-quoted)

@
VerbatimString_t ::=
  '\"\"\"' ~'\"\"\"' '\"\"\"'
;
@
 -}
verbatimStringLiteral :: MonadicParsing m => m (String, FC)
verbatimStringLiteral = token $ do (FC f start _) <- getFC
                                   try $ string "\"\"\""
                                   str <- manyTill anyChar $ try (string "\"\"\"")
                                   (FC _ _ end) <- getFC
                                   return (str, FC f start end)

{- | Parses a static modifier

@
Static ::=
  '%static'
;
@
-}
static :: IdrisParser Static
static =     do reserved "%static"; return Static
         <|> do reserved "[static]"
                fc <- getFC
                parserWarning fc Nothing (Msg "The use of [static] is deprecated, use %static instead.")
                return Static
         <|> return Dynamic
         <?> "static modifier"

{- | Parses a tactic script

@
Tactic ::= 'intro' NameList?
       |   'intros'
       |   'refine'      Name Imp+
       |   'mrefine'     Name
       |   'rewrite'     Expr
       |   'induction'   Expr
       |   'equiv'       Expr
       |   'let'         Name ':' Expr' '=' Expr
       |   'let'         Name           '=' Expr
       |   'focus'       Name
       |   'exact'       Expr
       |   'applyTactic' Expr
       |   'reflect'     Expr
       |   'fill'        Expr
       |   'try'         Tactic '|' Tactic
       |   '{' TacticSeq '}'
       |   'compute'
       |   'trivial'
       |   'solve'
       |   'attack'
       |   'state'
       |   'term'
       |   'undo'
       |   'qed'
       |   'abandon'
       |   ':' 'q'
       ;

Imp ::= '?' | '_';

TacticSeq ::=
    Tactic ';' Tactic
  | Tactic ';' TacticSeq
  ;
@
-}

-- | A specification of the arguments that tactics can take
data TacticArg = NameTArg -- ^ Names: n1, n2, n3, ... n
               | ExprTArg
               | AltsTArg
               | StringLitTArg

-- The FIXMEs are Issue #1766 in the issue tracker.
--     https://github.com/idris-lang/Idris-dev/issues/1766
-- | A list of available tactics and their argument requirements
tactics :: [([String], Maybe TacticArg, SyntaxInfo -> IdrisParser PTactic)]
tactics =
  [ (["intro"], Nothing, const $ -- FIXME syntax for intro (fresh name)
      do ns <- sepBy (spaced (fst <$> name)) (lchar ','); return $ Intro ns)
  , noArgs ["intros"] Intros
  , noArgs ["unfocus"] Unfocus
  , (["refine"], Just ExprTArg, const $
       do n <- spaced (fst <$> fnName)
          imps <- many imp
          return $ Refine n imps)
  , (["claim"], Nothing, \syn ->
       do n <- indentPropHolds gtProp *> (fst <$> name)
          goal <- indentPropHolds gtProp *> expr syn
          return $ Claim n goal)
  , (["mrefine"], Just ExprTArg, const $
       do n <- spaced (fst <$> fnName)
          return $ MatchRefine n)
  , expressionTactic ["rewrite"] Rewrite
  , expressionTactic ["case"] CaseTac
  , expressionTactic ["induction"] Induction
  , expressionTactic ["equiv"] Equiv
  , (["let"], Nothing, \syn -> -- FIXME syntax for let
       do n <- (indentPropHolds gtProp *> (fst <$> name))
          (do indentPropHolds gtProp *> lchar ':'
              ty <- indentPropHolds gtProp *> expr' syn
              indentPropHolds gtProp *> lchar '='
              t <- indentPropHolds gtProp *> expr syn
              i <- get
              return $ LetTacTy n (desugar syn i ty) (desugar syn i t))
            <|> (do indentPropHolds gtProp *> lchar '='
                    t <- indentPropHolds gtProp *> expr syn
                    i <- get
                    return $ LetTac n (desugar syn i t)))

  , (["focus"], Just ExprTArg, const $
       do n <- spaced (fst <$> name)
          return $ Focus n)
  , expressionTactic ["exact"] Exact
  , expressionTactic ["applyTactic"] ApplyTactic
  , expressionTactic ["byReflection"] ByReflection
  , expressionTactic ["reflect"] Reflect
  , expressionTactic ["fill"] Fill
  , (["try"], Just AltsTArg, \syn ->
        do t <- spaced (tactic syn)
           lchar '|'
           t1 <- spaced (tactic syn)
           return $ Try t t1)
  , noArgs ["compute"] Compute
  , noArgs ["trivial"] Trivial
  , noArgs ["unify"] DoUnify
  , (["search"], Nothing, const $
      do depth <- option 10 $ fst <$> natural
         return (ProofSearch True True (fromInteger depth) Nothing [] []))
  , noArgs ["implementation"] TCImplementation
  , noArgs ["solve"] Solve
  , noArgs ["attack"] Attack
  , noArgs ["state", ":state"] ProofState
  , noArgs ["term", ":term"] ProofTerm
  , noArgs ["undo", ":undo"] Undo
  , noArgs ["qed", ":qed"] Qed
  , noArgs ["abandon", ":q"] Abandon
  , noArgs ["skip"] Skip
  , noArgs ["sourceLocation"] SourceFC
  , expressionTactic [":e", ":eval"] TEval
  , expressionTactic [":t", ":type"] TCheck
  , expressionTactic [":search"] TSearch
  , (["fail"], Just StringLitTArg, const $
       do msg <- fst <$> stringLiteral
          return $ TFail [Idris.Core.TT.TextPart msg])
  , ([":doc"], Just ExprTArg, const $
       do whiteSpace
          doc <- (Right . fst <$> constant) <|> (Left . fst <$> fnName)
          eof
          return (TDocStr doc))
  ]
  where
  expressionTactic names tactic = (names, Just ExprTArg, \syn ->
     do t <- spaced (expr syn)
        i <- get
        return $ tactic (desugar syn i t))
  noArgs names tactic = (names, Nothing, const (return tactic))
  spaced parser = indentPropHolds gtProp *> parser
  imp :: IdrisParser Bool
  imp = do lchar '?'; return False
    <|> do lchar '_'; return True


tactic :: SyntaxInfo -> IdrisParser PTactic
tactic syn = choice [ do choice (map reserved names); parser syn
                    | (names, _, parser) <- tactics ]
          <|> do lchar '{'
                 t <- tactic syn;
                 lchar ';';
                 ts <- sepBy1 (tactic syn) (lchar ';')
                 lchar '}'
                 return $ TSeq t (mergeSeq ts)
          <|> ((lchar ':' >> empty) <?> "prover command")
          <?> "tactic"
  where
    mergeSeq :: [PTactic] -> PTactic
    mergeSeq [t]    = t
    mergeSeq (t:ts) = TSeq t (mergeSeq ts)

-- | Parses a tactic as a whole
fullTactic :: SyntaxInfo -> IdrisParser PTactic
fullTactic syn = do t <- tactic syn
                    eof
                    return t

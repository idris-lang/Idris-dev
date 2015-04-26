{-# LANGUAGE GeneralizedNewtypeDeriving, ConstraintKinds, PatternGuards #-}
module Idris.ParseExpr where

import Prelude hiding (pi)

import Text.Trifecta.Delta
import Text.Trifecta hiding (span, stringLiteral, charLiteral, natural, symbol, char, string, whiteSpace, Err)
import Text.Parser.LookAhead
import Text.Parser.Expression
import qualified Text.Parser.Token as Tok
import qualified Text.Parser.Char as Chr
import qualified Text.Parser.Token.Highlight as Hi

import Idris.AbsSyntax
import Idris.ParseHelpers
import Idris.ParseOps
import Idris.DSL

import Idris.Core.TT

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict

import Data.Function (on)
import Data.Maybe
import qualified Data.List.Split as Spl
import Data.List
import Data.Monoid
import Data.Char
import qualified Data.HashSet as HS
import qualified Data.Text as T
import qualified Data.ByteString.UTF8 as UTF8

import Debug.Trace

-- | Allow implicit type declarations
allowImp :: SyntaxInfo -> SyntaxInfo
allowImp syn = syn { implicitAllowed = True }

-- | Disallow implicit type declarations
disallowImp :: SyntaxInfo -> SyntaxInfo
disallowImp syn = syn { implicitAllowed = False }

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
                buildExpressionParser (table (idris_infixes i)) (expr' syn)

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
                      extensions syn (syntaxRulesList $ syntax_rules i)
                   <?> "user-defined expression"

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

data SynMatch = SynTm PTerm | SynBind Name

extension :: SyntaxInfo -> [Maybe (Name, SynMatch)] -> [Syntax] -> IdrisParser PTerm
extension syn ns rules =
  choice $ flip map (groupBy (ruleGroup `on` syntaxSymbols) rules) $ \rs ->
    case head rs of -- can never be []
      Rule (symb:_) _ _ -> try $ do
        n <- extensionSymbol symb
        extension syn (n : ns) [Rule ss t ctx | (Rule (_:ss) t ctx) <- rs]
      -- If we have more than one Rule in this bucket, our grammar is
      -- nondeterministic.
      Rule [] ptm _ -> return (flatten (update (mapMaybe id ns) ptm))
  where
    ruleGroup [] [] = True
    ruleGroup (s1:_) (s2:_) = s1 == s2
    ruleGroup _ _ = False

    extensionSymbol :: SSymbol -> IdrisParser (Maybe (Name, SynMatch))
    extensionSymbol (Keyword n)    = do reserved (show n); return Nothing
    extensionSymbol (Expr n)       = do tm <- expr syn
                                        return $ Just (n, SynTm tm)
    extensionSymbol (SimpleExpr n) = do tm <- simpleExpr syn
                                        return $ Just (n, SynTm tm)
    extensionSymbol (Binding n)    = do b <- name
                                        return $ Just (n, SynBind b)
    extensionSymbol (Symbol s)     = do symbol s
                                        return Nothing
    dropn :: Name -> [(Name, a)] -> [(Name, a)]
    dropn n [] = []
    dropn n ((x,t) : xs) | n == x = xs
                         | otherwise = (x,t):dropn n xs

    flatten :: PTerm -> PTerm -- flatten application
    flatten (PApp fc (PApp _ f as) bs) = flatten (PApp fc f (as ++ bs))
    flatten t = t

    updateB :: [(Name, SynMatch)] -> Name -> Name
    updateB ns n = case lookup n ns of
                     Just (SynBind t) -> t
                     _ -> n

    update :: [(Name, SynMatch)] -> PTerm -> PTerm
    update ns (PRef fc n) = case lookup n ns of
                              Just (SynTm t) -> t
                              _ -> PRef fc n
    update ns (PLam fc n ty sc)
      = PLam fc (updateB ns n) (update ns ty) (update (dropn n ns) sc)
    update ns (PPi p n ty sc)
      = PPi (updTacImp ns p) (updateB ns n)
            (update ns ty) (update (dropn n ns) sc)
    update ns (PLet fc n ty val sc) 
      = PLet fc (updateB ns n) (update ns ty)
              (update ns val) (update (dropn n ns) sc)
    update ns (PApp fc t args)
      = PApp fc (update ns t) (map (fmap (update ns)) args)
    update ns (PAppBind fc t args)
      = PAppBind fc (update ns t) (map (fmap (update ns)) args)
    update ns (PCase fc c opts)
      = PCase fc (update ns c) (map (pmap (update ns)) opts)
    update ns (PPair fc p l r) = PPair fc p (update ns l) (update ns r)
    update ns (PDPair fc p l t r)
      = PDPair fc p (update ns l) (update ns t) (update ns r)
    update ns (PAlternative a as) = PAlternative a (map (update ns) as)
    update ns (PHidden t) = PHidden (update ns t)
    update ns (PDoBlock ds) = PDoBlock $ upd ns ds
      where upd :: [(Name, SynMatch)] -> [PDo] -> [PDo]
            upd ns (DoExp fc t : ds) = DoExp fc (update ns t) : upd ns ds
            upd ns (DoBind fc n t : ds) = DoBind fc n (update ns t) : upd (dropn n ns) ds
            upd ns (DoLet fc n ty t : ds) = DoLet fc n (update ns ty) (update ns t)
                                                : upd (dropn n ns) ds
            upd ns (DoBindP fc i t ts : ds) 
                    = DoBindP fc (update ns i) (update ns t) 
                                 (map (\(l,r) -> (update ns l, update ns r)) ts)
                                                : upd ns ds
            upd ns (DoLetP fc i t : ds) = DoLetP fc (update ns i) (update ns t)
                                                : upd ns ds
    update ns (PGoal fc r n sc) = PGoal fc (update ns r) n (update ns sc)
    update ns t = t

    updTacImp ns (TacImp o st scr)  = TacImp o st (update ns scr)
    updTacImp _  x                  = x

{- | Parses a (normal) built-in expression
@
InternalExpr ::=
    UnifyLog
  | RecordType
  | SimpleExpr
  | Lambda
  | QuoteGoal
  | Let
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
impossible = PImpossible <$ reserved "impossible"

{- | Parses a case expression
@
CaseExpr ::=
  'case' Expr 'of' OpenBlock CaseOption+ CloseBlock;
@
-}
caseExpr :: SyntaxInfo -> IdrisParser PTerm
caseExpr syn = do reserved "case"; fc <- getFC
                  scr <- expr syn; reserved "of";
                  opts <- indentedBlock1 (caseOption syn)
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
caseOption syn = do lhs <- expr (syn { inPattern = True })
                    r <- impossible <|> symbol "=>" *> expr syn
                    return (lhs, r)
                 <?> "case option"

{- | Parses a proof block
@
ProofExpr ::=
  'proof' OpenBlock Tactic'* CloseBlock
  ;
@
-}
proofExpr :: SyntaxInfo -> IdrisParser PTerm
proofExpr syn = do reserved "proof"
                   ts <- indentedBlock1 (tactic syn)
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
tacticsExpr syn = do reserved "tactics"
                     ts <- indentedBlock1 (tactic syn)
                     return $ PTactics ts
                  <?> "tactics block"

{- | Parses a simple expression
@
SimpleExpr ::=
    {- External (User-defined) Simple Expression -}
  | '?' Name
  | % 'instance'
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
        <|> do x <- try (lchar '?' *> name); return (PMetavar x)
        <|> do lchar '%'; fc <- getFC; reserved "instance"; return (PResolveTC fc)
        <|> do reserved "Refl"; fc <- getFC;
               tm <- option Placeholder (do lchar '{'; t <- expr syn; lchar '}';
                                            return t)
               return (PRefl fc tm)
        <|> do reserved "elim_for"; fc <- getFC; t <- fnName; return (PRef fc (SN $ ElimN t))
        <|> proofExpr syn
        <|> tacticsExpr syn
        <|> try (do reserved "Type"; symbol "*"; return $ PUniverse AllTypes)
        <|> do reserved "AnyType"; return $ PUniverse AllTypes
        <|> do reserved "Type"; return PType
        <|> do reserved "UniqueType"; return $ PUniverse UniqueType
        <|> do reserved "NullType"; return $ PUniverse NullType
        <|> do c <- constant
               fc <- getFC
               return (modifyConst syn fc (PConstant c))
        <|> do symbol "'"; fc <- getFC; str <- name
               return (PApp fc (PRef fc (sUN "Symbol_"))
                          [pexp (PConstant (Str (show str)))])
        <|> do fc <- getFC
               x <- fnName
               if inPattern syn 
                  then option (PRef fc x)
                              (do reservedOp "@"
                                  s <- simpleExpr syn
                                  return (PAs fc x s))
                  else return (PRef fc x)
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

{- |Parses an expression in braces
@
Bracketed ::= '(' Bracketed'
@
 -}
bracketed :: SyntaxInfo -> IdrisParser PTerm
bracketed syn = do lchar '(' <?> "parenthesized expression"
                   bracketed' syn
{- |Parses the rest of an expression in braces
@
Bracketed' ::=
  ')'
  | Expr ')'
  | ExprList ')'
  | Expr '**' Expr ')'
  | Operator Expr ')'
  | Expr Operator ')'
  | Name ':' Expr '**' Expr ')'
  ;
@
-}
bracketed' :: SyntaxInfo -> IdrisParser PTerm
bracketed' syn =
            do lchar ')'
               fc <- getFC
               return $ PTrue fc TypeOrTerm
        <|> try (do ln <- name; lchar ':';
                    lty <- expr syn
                    reservedOp "**"
                    fc <- getFC
                    r <- expr syn
                    lchar ')'
                    return (PDPair fc TypeOrTerm (PRef fc ln) lty r))
        <|> try (do fc <- getFC; o <- operator; e <- expr syn; lchar ')'
                    -- No prefix operators! (bit of a hack here...)
                    if (o == "-" || o == "!")
                      then fail "minus not allowed in section"
                      else return $ PLam fc (sMN 1000 "ARG") Placeholder
                         (PApp fc (PRef fc (sUN o)) [pexp (PRef fc (sMN 1000 "ARG")),
                                                     pexp e]))
        <|> try (do l <- simpleExpr syn
                    op <- option Nothing (do o <- operator
                                             lchar ')'
                                             return (Just o)) 
                    fc0 <- getFC
                    case op of
                         Nothing -> bracketedExpr syn l
                         Just o -> return $ PLam fc0 (sMN 1000 "ARG") Placeholder
                             (PApp fc0 (PRef fc0 (sUN o)) [pexp l,
                                                           pexp (PRef fc0 (sMN 1000 "ARG"))]))
        <|> do l <- expr syn
               bracketedExpr syn l

bracketedExpr :: SyntaxInfo -> PTerm -> IdrisParser PTerm
bracketedExpr syn e =
             do lchar ')'; return e
        <|>  do fc <- do fc <- getFC
                         lchar ','
                         return fc
                rs <- sepBy1 (do fc' <- getFC; r <- expr syn; return (r, fc')) (lchar ',')
                lchar ')'
                return $ PPair fc TypeOrTerm e (mergePairs rs)
        <|>  do fc <- do fc <- getFC
                         reservedOp "**"
                         return fc
                r <- expr syn
                lchar ')'
                return (PDPair fc TypeOrTerm e Placeholder r)
        <?> "end of bracketed expression"
  where mergePairs :: [(PTerm, FC)] -> PTerm
        mergePairs [(t, fc)]    = t
        mergePairs ((t, fc):rs) = PPair fc TypeOrTerm t (mergePairs rs)

-- bit of a hack here. If the integer doesn't fit in an Int, treat it as a
-- big integer, otherwise try fromInteger and the constants as alternatives.
-- a better solution would be to fix fromInteger to work with Integer, as the
-- name suggests, rather than Int
{-| Finds optimal type for integer constant -}
modifyConst :: SyntaxInfo -> FC -> PTerm -> PTerm
modifyConst syn fc (PConstant (BI x))
    | not (inPattern syn)
        = PAlternative False
             (PApp fc (PRef fc (sUN "fromInteger")) [pexp (PConstant (BI (fromInteger x)))]
             : consts)
    | otherwise = PAlternative False consts
    where
      consts = [ PConstant (BI x)
               , PConstant (I (fromInteger x))
               , PConstant (B8 (fromInteger x))
               , PConstant (B16 (fromInteger x))
               , PConstant (B32 (fromInteger x))
               , PConstant (B64 (fromInteger x))
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
alt syn = do symbol "(|"; alts <- sepBy1 (expr' syn) (lchar ','); symbol "|)"
             return (PAlternative False alts)

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
unifyLog syn = do try (lchar '%' *> reserved "unifyLog")
                  tm <- simpleExpr syn
                  return (PUnifyLog tm)
               <?> "unification log expression"

{- | Parses a new-style tactics expression
RunTactics ::=
  '%' 'runElab' SimpleExpr
  ;
-}
runElab :: SyntaxInfo -> IdrisParser PTerm
runElab syn = do try (lchar '%' *> reserved "runElab")
                 fc <- getFC
                 tm <- simpleExpr syn
                 i <- get
                 return $ PRunElab fc tm
              <?> "new-style tactics expression"

{- | Parses a disambiguation expression 
Disamb ::=
  '%' 'disamb' NameList Expr
  ;
-}
disamb :: SyntaxInfo -> IdrisParser PTerm
disamb syn = do reserved "with";
                ns <- sepBy1 name (lchar ',')
                tm <- expr' syn
                return (PDisamb (map tons ns) tm)
               <?> "unification log expression"
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
                 ff <- fnName
                 return (PLet fc (sMN 0 "match")
                               f
                               (PMatchApp fc ff)
                               (PRef fc (sMN 0 "match")))
              <?> "matching application expression") <|> (do
             fc <- getFC
             i <- get
             args <- many (do notEndApp; arg syn)
             case args of
               [] -> return f
               _  -> return (PApp fc f args))
       <?> "function application"

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
                     n <- name
                     fc <- getFC
                     v <- option (PRef fc n) (do lchar '='
                                                 expr syn)
                     lchar '}'
                     return (pimp n v True)
                  <?> "implicit function argument"

{-| Parses a constraint argument (for selecting a named type class instance)

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
quasiquote syn = do symbol "`("
                    e <- expr syn { syn_in_quasiquote = (syn_in_quasiquote syn) + 1 ,
                                    inPattern = False }
                    g <- optional $ do
                           symbol ":"
                           expr syn { inPattern = False } -- don't allow antiquotes
                    symbol ")"
                    return $ PQuasiquote e g
                 <?> "quasiquotation"

{-| Parses an unquoting inside a quasiquotation (for building reflected terms using the elaborator)

> Unquote ::= ',' Expr

-}
unquote :: SyntaxInfo -> IdrisParser PTerm
unquote syn = do guard (syn_in_quasiquote syn > 0)
                 symbol "~"
                 e <- simpleExpr syn { syn_in_quasiquote = syn_in_quasiquote syn - 1 }
                 return $ PUnquote e
              <?> "unquotation"

{-| Parses a quotation of a name (for using the elaborator to resolve boring details)

> NameQuote ::= '`{' Name '}'

-}
namequote :: SyntaxInfo -> IdrisParser PTerm
namequote syn = do symbol "`{"
                   n <- fnName
                   symbol "}"
                   return $ PQuoteName n
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
recordType :: SyntaxInfo -> IdrisParser PTerm
recordType syn = 
      do reserved "record"
         lchar '{'
         fgs <- fieldGetOrSet
         lchar '}'
         fc <- getFC
         rec <- optional (simpleExpr syn)
         case fgs of
              Left fields ->
                case rec of
                   Nothing ->
                       return (PLam fc (sMN 0 "fldx") Placeholder
                                   (applyAll fc fields (PRef fc (sMN 0 "fldx"))))
                   Just v -> return (applyAll fc fields v)
              Right fields ->
                case rec of
                   Nothing ->
                       return (PLam fc (sMN 0 "fldx") Placeholder
                                 (getAll fc (reverse fields) 
                                     (PRef fc (sMN 0 "fldx"))))
                   Just v -> return (getAll fc (reverse fields) v)

       <?> "record setting expression"
   where fieldSet :: IdrisParser ([Name], PTerm)
         fieldSet = do ns <- fieldGet
                       lchar '='
                       e <- expr syn
                       return (ns, e)
                    <?> "field setter"

         fieldGet :: IdrisParser [Name]
         fieldGet = sepBy1 fnName (symbol "->")

         fieldGetOrSet :: IdrisParser (Either [([Name], PTerm)] [Name])
         fieldGetOrSet = try (do fs <- sepBy1 fieldSet (lchar ',')
                                 return (Left fs))
                     <|> do f <- fieldGet
                            return (Right f)

         applyAll :: FC -> [([Name], PTerm)] -> PTerm -> PTerm
         applyAll fc [] x = x
         applyAll fc ((ns, e) : es) x
            = applyAll fc es (doUpdate fc ns e x)
            
         doUpdate fc [n] e get
              = PApp fc (PRef fc (mkType n)) [pexp e, pexp get]
         doUpdate fc (n : ns) e get
              = PApp fc (PRef fc (mkType n)) 
                  [pexp (doUpdate fc ns e (PApp fc (PRef fc n) [pexp get])), 
                   pexp get]

         getAll :: FC -> [Name] -> PTerm -> PTerm
         getAll fc [n] e = PApp fc (PRef fc n) [pexp e]
         getAll fc (n:ns) e = PApp fc (PRef fc n) [pexp (getAll fc ns e)]


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
                  sc <- expr syn
                  return (bindList (PPi constraint) cs sc)
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
                ((do xt <- try $ tyOptDeclList syn
                     fc <- getFC
                     sc <- lambdaTail
                     return (bindList (PLam fc) xt sc))
                 <|>
                 (do ps <- sepBy (do fc <- getFC
                                     e <- simpleExpr (syn { inPattern = True })
                                     return (fc, e))
                                 (lchar ',')
                     sc <- lambdaTail
                     return (pmList (zip [0..] ps) sc)))
                  <?> "lambda expression"
    where pmList :: [(Int, (FC, PTerm))] -> PTerm -> PTerm
          pmList [] sc = sc
          pmList ((i, (fc, x)) : xs) sc
                = PLam fc (sMN i "lamp") Placeholder
                        (PCase fc (PRef fc (sMN i "lamp"))
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
rewriteTerm syn = do reserved "rewrite"
                     fc <- getFC
                     prf <- expr syn
                     giving <- optional (do symbol "==>"; expr' syn)
                     reserved "in";  sc <- expr syn
                     return (PRewrite fc
                             (PApp fc (PRef fc (sUN "sym")) [pexp prf]) sc
                               giving)
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
let_ syn = try (do reserved "let"
                   ls <- indentedBlock (let_binding syn)
                   reserved "in";  sc <- expr syn
                   return (buildLets ls sc))
           <?> "let binding"
  where buildLets [] sc = sc
        buildLets ((fc,PRef _ n,ty,v,[]):ls) sc
          = PLet fc n ty v (buildLets ls sc)
        buildLets ((fc,pat,ty,v,alts):ls) sc
          = PCase fc v ((pat, buildLets ls sc) : alts)

let_binding syn = do fc <- getFC; 
                     pat <- expr' (syn { inPattern = True })
                     ty <- option Placeholder (do lchar ':'; expr' syn)
                     lchar '='
                     v <- expr syn
                     ts <- option [] (do lchar '|'
                                         sepBy1 (do_alt syn) (lchar '|'))
                     return (fc,pat,ty,v,ts)
                  

{- | Parses a quote goal

@
QuoteGoal ::=
  'quoteGoal' Name 'by' Expr 'in' Expr
  ;
@
 -}
quoteGoal :: SyntaxInfo -> IdrisParser PTerm
quoteGoal syn = do reserved "quoteGoal"; n <- name;
                   reserved "by"
                   r <- expr syn
                   reserved "in"
                   fc <- getFC
                   sc <- expr syn
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
          return (Exp opts st False)

explicitPi opts st syn
   = do xt <- try (lchar '(' *> typeDeclList syn <* lchar ')')
        binder <- bindsymbol opts st syn
        sc <- expr syn
        return (bindList (PPi binder) xt sc)
       
autoImplicit opts st syn
   = do reserved "auto"
        when (st == Static) $ fail "auto implicits can not be static"
        xt <- typeDeclList syn
        lchar '}'
        symbol "->"
        sc <- expr syn
        return (bindList (PPi
          (TacImp [] Dynamic (PTactics [ProofSearch True True 100 Nothing []]))) xt sc) 

defaultImplicit opts st syn = do
   reserved "default"
   when (st == Static) $ fail "default implicits can not be static"
   ist <- get
   script' <- simpleExpr syn
   let script = debindApp syn . desugar syn ist $ script'
   xt <- typeDeclList syn
   lchar '}'
   symbol "->"
   sc <- expr syn
   return (bindList (PPi (TacImp [] Dynamic script)) xt sc)

normalImplicit opts st syn = do
   xt <- typeDeclList syn <* lchar '}'
   symbol "->"
   cs <- constraintList syn
   sc <- expr syn
   let (im,cl)
          = if implicitAllowed syn
               then (Imp opts st False Nothing,
                      constraint)
               else (Imp opts st False (Just (Impl False)),
                     Imp opts st False (Just (Impl True)))
   return (bindList (PPi im) xt 
           (bindList (PPi cl) cs sc))

implicitPi opts st syn = 
      autoImplicit opts st syn
        <|> defaultImplicit opts st syn
          <|> normalImplicit opts st syn

unboundPi opts st syn = do
       x <- opExpr syn
       (do binder <- bindsymbol opts st syn
           sc <- expr syn
           return (PPi binder (sUN "__pi_arg") x sc))
              <|> return x

pi :: SyntaxInfo -> IdrisParser PTerm
pi syn =
     do opts <- piOpts syn
        st   <- static
        explicitPi opts st syn
         <|> try (do lchar '{'; implicitPi opts st syn)
            <|> unboundPi opts st syn
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
constraintList :: SyntaxInfo -> IdrisParser [(Name, PTerm)]
constraintList syn = try (constraintList1 syn)
                     <|> return []

constraintList1 :: SyntaxInfo -> IdrisParser [(Name, PTerm)]
constraintList1 syn = try (do lchar '('
                              tys <- sepBy1 nexpr (lchar ',')
                              lchar ')'
                              reservedOp "=>"
                              return tys)
                  <|> try (do t <- opExpr (disallowImp syn)
                              reservedOp "=>"
                              return [(defname, t)])
                  <?> "type constraint list"
  where nexpr = try (do n <- name; lchar ':'
                        e <- expr syn
                        return (n, e))
                <|> do e <- expr syn
                       return (defname, e)
        defname = sMN 0 "constrarg"

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
typeDeclList :: SyntaxInfo -> IdrisParser [(Name, PTerm)]
typeDeclList syn = try (sepBy1 (do x <- fnName
                                   lchar ':'
                                   t <- typeExpr (disallowImp syn)
                                   return (x,t))
                           (lchar ','))
                   <|> do ns <- sepBy1 name (lchar ',')
                          lchar ':'
                          t <- typeExpr (disallowImp syn)
                          return (map (\x -> (x, t)) ns)
                   <?> "type declaration list"

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
tyOptDeclList :: SyntaxInfo -> IdrisParser [(Name, PTerm)]
tyOptDeclList syn = sepBy1 (do x <- nameOrPlaceholder
                               t <- option Placeholder (do lchar ':'
                                                           expr syn)
                               return (x,t))
                           (lchar ',')
                    <?> "type declaration list"
    where  nameOrPlaceholder :: IdrisParser Name
           nameOrPlaceholder = fnName
                           <|> do symbol "_"
                                  return (sMN 0 "underscore")
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
listExpr syn = do lchar '['; fc <- getFC;
                  try ((lchar ']' <?> "end of list expression") *> return (mkList fc [])) <|> (do
                    x <- expr syn <?> "expression"
                    (do try (lchar '|') <?> "list comprehension"
                        qs <- sepBy1 (do_ syn) (lchar ',')
                        lchar ']'
                        return (PDoBlock (map addGuard qs ++
                                   [DoExp fc (PApp fc (PRef fc (sUN "return"))
                                                [pexp x])]))) <|> (do
                          xs <- many ((lchar ',' <?> "list element") *> expr syn)
                          lchar ']' <?> "end of list expression"
                          return (mkList fc (x:xs))))
                <?> "list expression"
  where
    mkList :: FC -> [PTerm] -> PTerm
    mkList fc [] = PRef fc (sUN "Nil")
    mkList fc (x : xs) = PApp fc (PRef fc (sUN "::")) [pexp x, pexp (mkList fc xs)]
    addGuard :: PDo -> PDo
    addGuard (DoExp fc e) = DoExp fc (PApp fc (PRef fc (sUN "guard"))
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
    = do reserved "do"
         ds <- indentedBlock1 (do_ syn)
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
     = try (do reserved "let"
               i <- name
               ty <- option Placeholder (do lchar ':'
                                            expr' syn)
               reservedOp "="
               fc <- getFC
               e <- expr syn
               return (DoLet fc i ty e))
   <|> try (do reserved "let"
               i <- expr' syn
               reservedOp "="
               fc <- getFC
               sc <- expr syn
               return (DoLetP fc i sc))
   <|> try (do i <- name
               symbol "<-"
               fc <- getFC
               e <- expr syn;
               option (DoBind fc i e)
                      (do lchar '|'
                          ts <- sepBy1 (do_alt syn) (lchar '|')
                          return (DoBindP fc (PRef fc i) e ts)))
   <|> try (do i <- expr' syn
               symbol "<-"
               fc <- getFC
               e <- expr syn;
               option (DoBindP fc i e [])
                      (do lchar '|'
                          ts <- sepBy1 (do_alt syn) (lchar '|')
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
         e <- expr syn
         symbol "|]"
         return (PIdiom fc e)
      <?> "expression in idiom brackets"

{- |Parses a constant or literal expression

@
Constant ::=
    'Integer'
  | 'Int'
  | 'Char'
  | 'Float'
  | 'String'
  | 'Ptr'
  | 'ManagedPtr'
  | 'prim__UnsafeBuffer'
  | 'Bits8'
  | 'Bits16'
  | 'Bits32'
  | 'Bits64'
  | 'Bits8x16'
  | 'Bits16x8'
  | 'Bits32x4'
  | 'Bits64x2'
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
--   , ("Ptr",                PtrType)
--   , ("ManagedPtr",         ManagedPtrType)
  , ("prim__WorldType",    WorldType)
  , ("prim__TheWorld",     TheWorld)
  , ("Bits8",              AType (ATInt (ITFixed IT8)))
  , ("Bits16",             AType (ATInt (ITFixed IT16)))
  , ("Bits32",             AType (ATInt (ITFixed IT32)))
  , ("Bits64",             AType (ATInt (ITFixed IT64)))
  ]
 
constant :: IdrisParser Idris.Core.TT.Const
constant = choice [ do reserved name; return ty | (name, ty) <- constants ]
        <|> do f <- try float;   return $ Fl f
        <|> do i <- natural; return $ BI i
        <|> do s <- verbatimStringLiteral; return $ Str s
        <|> do s <- stringLiteral;  return $ Str s
        <|> do c <- try charLiteral; return $ Ch c --Currently ambigous with symbols
        <?> "constant or literal"

{- | Parses a verbatim multi-line string literal (triple-quoted)

@
VerbatimString_t ::=
  '\"\"\"' ~'\"\"\"' '\"\"\"'
;
@
 -}
verbatimStringLiteral :: MonadicParsing m => m String
verbatimStringLiteral = token $ do try $ string "\"\"\""
                                   manyTill anyChar $ try (string "\"\"\"")

{- | Parses a static modifier

@
Static ::=
  '[' static ']'
;
@
-}
static :: IdrisParser Static
static =     do reserved "[static]"; return Static
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
      do ns <- sepBy (spaced name) (lchar ','); return $ Intro ns)
  , noArgs ["intros"] Intros
  , noArgs ["unfocus"] Unfocus
  , (["refine"], Just ExprTArg, const $
       do n <- spaced fnName
          imps <- many imp
          return $ Refine n imps)
  , (["claim"], Nothing, \syn ->
       do n <- indentPropHolds gtProp *> name
          goal <- indentPropHolds gtProp *> expr syn
          return $ Claim n goal)
  , (["mrefine"], Just ExprTArg, const $
       do n <- spaced fnName
          return $ MatchRefine n)
  , expressionTactic ["rewrite"] Rewrite
  , expressionTactic ["case"] CaseTac
  , expressionTactic ["induction"] Induction
  , expressionTactic ["equiv"] Equiv
  , (["let"], Nothing, \syn -> -- FIXME syntax for let
       do n <- (indentPropHolds gtProp *> name)
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
       do n <- spaced name
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
      do depth <- option 10 natural
         return (ProofSearch True True (fromInteger depth) Nothing []))
  , noArgs ["instance"] TCInstance
  , noArgs ["solve"] Solve
  , noArgs ["attack"] Attack
  , noArgs ["state"] ProofState
  , noArgs ["term"] ProofTerm
  , noArgs ["undo"] Undo
  , noArgs ["qed"] Qed
  , noArgs ["abandon", ":q"] Abandon
  , noArgs ["skip"] Skip
  , noArgs ["sourceLocation"] SourceFC
  , expressionTactic [":e", ":eval"] TEval
  , expressionTactic [":t", ":type"] TCheck
  , expressionTactic [":search"] TSearch
  , (["fail"], Just StringLitTArg, const $
       do msg <- stringLiteral
          return $ TFail [Idris.Core.TT.TextPart msg])
  , ([":doc"], Just ExprTArg, const $
       do whiteSpace
          doc <- (Right <$> constant) <|> (Left <$> fnName)
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


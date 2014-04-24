{-# LANGUAGE GeneralizedNewtypeDeriving, ConstraintKinds, PatternGuards #-}
{-# OPTIONS_GHC -O0 #-}
module Idris.ParseExpr where

import Prelude hiding (pi)

import Text.Trifecta.Delta
import Text.Trifecta hiding (span, stringLiteral, charLiteral, natural, symbol, char, string, whiteSpace)
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
                      extensions syn (syntax_rules i)
                   <?> "user-defined expression"

{- | Parses a simple user-defined expression -}
simpleExternalExpr :: SyntaxInfo -> IdrisParser PTerm
simpleExternalExpr syn = do i <- get
                            extensions syn (filter isSimple (syntax_rules i))
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
extensions syn rules = choice (map (try . extension syn) (filter isValid rules))
                       <?> "user-defined expression"
  where
    isValid :: Syntax -> Bool
    isValid (Rule _ _ AnySyntax) = True
    isValid (Rule _ _ PatternSyntax) = inPattern syn
    isValid (Rule _ _ TermSyntax) = not (inPattern syn)


data SynMatch = SynTm PTerm | SynBind Name

{- | Tries to parse an expression given a user-defined rule -}
extension :: SyntaxInfo -> Syntax -> IdrisParser PTerm
extension syn (Rule ssym ptm _)
    = do smap <- mapM extensionSymbol ssym
         let ns = mapMaybe id smap
         return (flatten (update ns ptm)) -- updated with smap
  where
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
    update ns (PLam n ty sc)
      = PLam (updateB ns n) (update ns ty) (update (dropn n ns) sc)
    update ns (PPi p n ty sc)
      = PPi (updTacImp ns p) (updateB ns n)
            (update ns ty) (update (dropn n ns) sc)
    update ns (PLet n ty val sc) 
      = PLet  (updateB ns n) (update ns ty)
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
  Expr '=>' Expr Terminator
  ;
@
-}
caseOption :: SyntaxInfo -> IdrisParser (PTerm, PTerm)
caseOption syn = do lhs <- expr (syn { inPattern = True })
                    symbol "=>"; r <- expr syn
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
  | 'refl' ('{' Expr '}')?
  | ProofExpr
  | TacticsExpr
  | FnName
  | Idiom
  | List
  | Alt
  | Bracketed
  | Constant
  | Type
  | '_|_'
  | '_'
  ;
@
-}
simpleExpr :: SyntaxInfo -> IdrisParser PTerm
simpleExpr syn =
            try (simpleExternalExpr syn)
        <|> do x <- try (lchar '?' *> name); return (PMetavar x)
        <|> do lchar '%'; fc <- getFC; reserved "instance"; return (PResolveTC fc)
        <|> do reserved "refl"; fc <- getFC;
               tm <- option Placeholder (do lchar '{'; t <- expr syn; lchar '}';
                                            return t)
               return (PRefl fc tm)
        <|> do reserved "elim_for"; fc <- getFC; t <- fnName; return (PRef fc (SN $ ElimN t))
        <|> proofExpr syn
        <|> tacticsExpr syn
        <|> do reserved "Type"; return PType
        <|> do c <- constant
               fc <- getFC
               return (modifyConst syn fc (PConstant c))
        <|> do symbol "'"; fc <- getFC; str <- name
               return (PApp fc (PRef fc (sUN "Symbol_"))
                          [pexp (PConstant (Str (show str)))])
        <|> do fc <- getFC
               x <- fnName
               return (PRef fc x)
        <|> idiom syn
        <|> listExpr syn
        <|> alt syn
        <|> do lchar '!'
               s <- simpleExpr syn
               fc <- getFC
               return (PAppBind fc s [])
        <|> bracketed (disallowImp syn)
        <|> do symbol "_|_"
               fc <- getFC
               return (PFalse fc)
        <|> do lchar '_'; return Placeholder
        <?> "expression"

{- |Parses an expression in braces
@
Bracketed ::= '(' Bracketed'
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
                      else return $ PLam (sMN 1000 "ARG") Placeholder
                         (PApp fc (PRef fc (sUN o)) [pexp (PRef fc (sMN 1000 "ARG")),
                                                     pexp e]))
        <|> try (do l <- simpleExpr syn
                    op <- option Nothing (do o <- operator
                                             lchar ')'
                                             return (Just o)) 
                    fc0 <- getFC
                    case op of
                         Nothing -> bracketedExpr syn l
                         Just o -> return $ PLam (sMN 1000 "ARG") Placeholder
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
app syn = do f <- reserved "mkForeign"
             fc <- getFC
             fn <- arg syn
             args <- many (do notEndApp; arg syn)
             i <- get
             let ap = PApp fc (PRef fc (sUN "liftPrimIO"))
                       [pexp (PLam (sMN 0 "w")
                             Placeholder
                             (PApp fc (PRef fc (sUN "mkForeignPrim"))
                                         (fn : args ++
                                            [pexp (PRef fc (sMN 0 "w"))])))]
             return (dslify i ap)

       <|> do f <- simpleExpr syn
              (do try $ symbol "<=="
                  fc <- getFC
                  ff <- fnName
                  return (PLet (sMN 0 "match")
                                f
                                (PMatchApp fc ff)
                                (PRef fc (sMN 0 "match")))
               <?> "matching application expression") <|> (do
              fc <- getFC
              i <- get
              args <- many (do notEndApp; arg syn)
              case args of
                [] -> return f
                _  -> return (dslify i (PApp fc f args)))
       <?> "function application"
  where
    dslify :: IState -> PTerm -> PTerm
    dslify i (PApp fc (PRef _ f) [a])
        | [d] <- lookupCtxt f (idris_dsls i)
            = desugar (syn { dsl_info = d }) i (getTm a)
    dslify i t = t

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
recordType syn
    = do reserved "record"
         lchar '{'
         fields <- sepBy1 fieldType (lchar ',')
         lchar '}'
         fc <- getFC
         rec <- optional (simpleExpr syn)
         case rec of
            Nothing ->
                return (PLam (sMN 0 "fldx") Placeholder
                            (applyAll fc fields (PRef fc (sMN 0 "fldx"))))
            Just v -> return (applyAll fc fields v)
       <?> "record setting expression"
   where fieldType :: IdrisParser (Name, PTerm)
         fieldType = do n <- fnName
                        lchar '='
                        e <- expr syn
                        return (n, e)
                     <?> "field setter"
         applyAll :: FC -> [(Name, PTerm)] -> PTerm -> PTerm
         applyAll fc [] x = x
         applyAll fc ((n, e) : es) x
            = applyAll fc es (PApp fc (PRef fc (mkType n)) [pexp e, pexp x])

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
                  return (bindList (PPi constraint) (map (\x -> (sMN 0 "constrarg", x)) cs) sc)
               <?> "type signature"

{- | Parses a lambda expression
@
Lambda ::=
    '\\' TypeOptDeclList '=>' Expr
  | '\\' SimpleExprList  '=>' Expr
  ;
@
@
SimpleExprList ::=
  SimpleExpr
  | SimpleExpr ',' SimpleExprList
  ;
@
-}
lambda :: SyntaxInfo -> IdrisParser PTerm
lambda syn = do lchar '\\' <?> "lambda expression"
                (do xt <- try $ tyOptDeclList syn
                    symbol "=>"
                    sc <- expr syn
                    return (bindList PLam xt sc)) <|> do
                      ps <- sepBy (do fc <- getFC
                                      e <- simpleExpr syn
                                      return (fc, e)) (lchar ',')
                      symbol "=>"
                      sc <- expr syn
                      return (pmList (zip [0..] ps) sc)
                 <?> "lambda expression"
    where pmList :: [(Int, (FC, PTerm))] -> PTerm -> PTerm
          pmList [] sc = sc
          pmList ((i, (fc, x)) : xs) sc
                = PLam (sMN i "lamp") Placeholder
                        (PCase fc (PRef fc (sMN i "lamp"))
                                [(x, pmList xs sc)])

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
let_ syn = try (do reserved "let"; fc <- getFC; n <- name;
                   ty <- option Placeholder (do lchar ':'; expr' syn)
                   lchar '='
                   v <- expr syn
                   ts <- option [] (do lchar '|'
                                       sepBy1 (do_alt syn) (lchar '|'))
                   reserved "in";  sc <- expr syn
                   case ts of
                        [] -> return (PLet n ty v sc)
                        alts -> return (PCase fc v ((PRef fc n, sc) : ts)))
           <|> (do reserved "let"; fc <- getFC; pat <- expr' (syn { inPattern = True } )
                   symbol "="; v <- expr syn
                   ts <- option [] (do lchar '|'
                                       sepBy1 (do_alt syn) (lchar '|'))
                   reserved "in"; sc <- expr syn
                   return (PCase fc v ((pat, sc) : ts)))
           <?> "let binding"

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

pi :: SyntaxInfo -> IdrisParser PTerm
pi syn =
     do opts <- piOpts syn
        st   <- static
        (do xt <- try (lchar '(' *> typeDeclList syn <* lchar ')')
            symbol "->"
            sc <- expr syn
            return (bindList (PPi (Exp opts st False)) xt sc)) <|> (do
               (do try (lchar '{' *> reserved "auto")
                   when (st == Static) $ fail "auto type constraints can not be lazy or static"
                   xt <- typeDeclList syn
                   lchar '}'
                   symbol "->"
                   sc <- expr syn
                   return (bindList (PPi
                     (TacImp [] Dynamic (PTactics [Trivial]))) xt sc)) <|> (do
                       try (lchar '{' *> reserved "default")
                       when (st == Static) $ fail "default tactic constraints can not be lazy or static"
                       script <- simpleExpr syn
                       xt <- typeDeclList syn
                       lchar '}'
                       symbol "->"
                       sc <- expr syn
                       return (bindList (PPi (TacImp [] Dynamic script)) xt sc))
                 <|> (if implicitAllowed syn then do
                            xt <- try (lchar '{' *> typeDeclList syn <* lchar '}')
                            symbol "->"
                            sc <- expr syn
                            return (bindList (PPi (Imp opts st False)) xt sc)
                       else do fail "no implicit arguments allowed here"))
                 <|> (do x <- opExpr syn
                         (do symbol "->"
                             sc <- expr syn
                             return (PPi (Exp opts st False) (sUN "__pi_arg") x sc))
                          <|> return x)
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
constraintList :: SyntaxInfo -> IdrisParser [PTerm]
constraintList syn = try (do lchar '('
                             tys <- sepBy1 (expr' (disallowImp syn)) (lchar ',')
                             lchar ')'
                             reservedOp "=>"
                             return tys)
                 <|> try (do t <- expr (disallowImp syn)
                             reservedOp "=>"
                             return [t])
                 <|> return []
                 <?> "type constraint list"

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
         ds <- indentedBlock (do_ syn)
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
                symbol "=>"
                r <- expr' syn
                return (l, r)

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
constant :: IdrisParser Idris.Core.TT.Const
constant =  do reserved "Integer";      return (AType (ATInt ITBig))
        <|> do reserved "Int";          return (AType (ATInt ITNative))
        <|> do reserved "Char";         return (AType (ATInt ITChar))
        <|> do reserved "Float";        return (AType ATFloat)
        <|> do reserved "String";       return StrType
        <|> do reserved "Ptr";          return PtrType
        <|> do reserved "ManagedPtr";   return ManagedPtrType
        <|> do reserved "prim__UnsafeBuffer"; return BufferType
        <|> do reserved "Bits8";  return (AType (ATInt (ITFixed IT8)))
        <|> do reserved "Bits16"; return (AType (ATInt (ITFixed IT16)))
        <|> do reserved "Bits32"; return (AType (ATInt (ITFixed IT32)))
        <|> do reserved "Bits64"; return (AType (ATInt (ITFixed IT64)))
        <|> do reserved "Bits8x16"; return (AType (ATInt (ITVec IT8 16)))
        <|> do reserved "Bits16x8"; return (AType (ATInt (ITVec IT16 8)))
        <|> do reserved "Bits32x4"; return (AType (ATInt (ITVec IT32 4)))
        <|> do reserved "Bits64x2"; return (AType (ATInt (ITVec IT64 2)))
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

tactic :: SyntaxInfo -> IdrisParser PTactic
tactic syn = do reserved "intro"; ns <- sepBy (indentPropHolds gtProp *> name) (lchar ',')
                return $ Intro ns
          <|> do reserved "intros"; return Intros
          <|> try (do reserved "refine"; n <- (indentPropHolds gtProp *> fnName)
                      imps <- some imp
                      return $ Refine n imps)
          <|> do reserved "refine"; n <- (indentPropHolds gtProp *> fnName)
                 i <- get
                 return $ Refine n []
          <|> do reserved "mrefine"; n <- (indentPropHolds gtProp *> fnName)
                 i <- get
                 return $ MatchRefine n
          <|> do reserved "rewrite"; t <- (indentPropHolds gtProp *> expr syn);
                 i <- get
                 return $ Rewrite (desugar syn i t)
          <|> do reserved "induction"; nm <- (indentPropHolds gtProp *> fnName);
                 return $ Induction nm
          <|> do reserved "equiv"; t <- (indentPropHolds gtProp *> expr syn);
                 i <- get
                 return $ Equiv (desugar syn i t)
          <|> try (do reserved "let"; n <- (indentPropHolds gtProp *> name); (indentPropHolds gtProp *> lchar ':');
                      ty <- (indentPropHolds gtProp *> expr' syn); (indentPropHolds gtProp *> lchar '='); t <- (indentPropHolds gtProp *> expr syn);
                      i <- get
                      return $ LetTacTy n (desugar syn i ty) (desugar syn i t))
          <|> try (do reserved "let"; n <- (indentPropHolds gtProp *> name); (indentPropHolds gtProp *> lchar '=');
                      t <- (indentPropHolds gtProp *> expr syn);
                      i <- get
                      return $ LetTac n (desugar syn i t))
          <|> do reserved "focus"; n <- (indentPropHolds gtProp *> name)
                 return $ Focus n
          <|> do reserved "exact"; t <- (indentPropHolds gtProp *> expr syn);
                 i <- get
                 return $ Exact (desugar syn i t)
          <|> do reserved "applyTactic"; t <- (indentPropHolds gtProp *> expr syn);
                 i <- get
                 return $ ApplyTactic (desugar syn i t)
          <|> do reserved "byReflection"; t <- (indentPropHolds gtProp *> expr syn);
                 i <- get
                 return $ ByReflection (desugar syn i t)
          <|> do reserved "reflect"; t <- (indentPropHolds gtProp *> expr syn);
                 i <- get
                 return $ Reflect (desugar syn i t)
          <|> do reserved "fill"; t <- (indentPropHolds gtProp *> expr syn);
                 i <- get
                 return $ Fill (desugar syn i t)
          <|> do reserved "try"; t <- (indentPropHolds gtProp *> tactic syn);
                 lchar '|';
                 t1 <- (indentPropHolds gtProp *> tactic syn)
                 return $ Try t t1
          <|> do lchar '{'
                 t <- tactic syn;
                 lchar ';';
                 ts <- sepBy1 (tactic syn) (lchar ';')
                 lchar '}'
                 return $ TSeq t (mergeSeq ts)
          <|> do reserved "compute"; return Compute
          <|> do reserved "trivial"; return Trivial
          <|> do reserved "unify"; return DoUnify
          <|> do reserved "search"; return (ProofSearch True Nothing [])
          <|> do reserved "instance"; return TCInstance
          <|> do reserved "solve"; return Solve
          <|> do reserved "attack"; return Attack
          <|> do reserved "state"; return ProofState
          <|> do reserved "term"; return ProofTerm
          <|> do reserved "undo"; return Undo
          <|> do reserved "qed"; return Qed
          <|> do reserved "abandon"; return Abandon
          <|> do lchar ':';
                 (    (do reserved "q"; return Abandon)
                  <|> (do (reserved "e" <|> reserved "eval");
                          t <- (indentPropHolds gtProp *> expr syn);
                          i <- get
                          return $ TEval (desugar syn i t))
                  <|> (do (reserved "t" <|> reserved "type");
                          t <- (indentPropHolds gtProp *> expr syn);
                          i <- get
                          return $ TCheck (desugar syn i t))
                  <?> "prover command")
          <?> "tactic"
  where
    imp :: IdrisParser Bool
    imp = do lchar '?'; return False
      <|> do lchar '_'; return True
    mergeSeq :: [PTactic] -> PTactic
    mergeSeq [t]    = t
    mergeSeq (t:ts) = TSeq t (mergeSeq ts)

-- | Parses a tactic as a whole
fullTactic :: SyntaxInfo -> IdrisParser PTactic
fullTactic syn = do t <- tactic syn
                    eof
                    return t

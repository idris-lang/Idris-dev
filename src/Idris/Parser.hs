{-# LANGUAGE GeneralizedNewtypeDeriving, ConstraintKinds, PatternGuards #-}
{-# OPTIONS_GHC -O0 #-}
module Idris.Parser(module Idris.Parser,
                    module Idris.ParseExpr,
                    module Idris.ParseData,
                    module Idris.ParseHelpers,
                    module Idris.ParseOps) where

import Prelude hiding (pi)

import Text.Trifecta.Delta
import Text.Trifecta hiding (span, stringLiteral, charLiteral, natural, symbol, char, string, whiteSpace)
import Text.Parser.LookAhead
import Text.Parser.Expression
import qualified Text.Parser.Token as Tok
import qualified Text.Parser.Char as Chr
import qualified Text.Parser.Token.Highlight as Hi

import Text.PrettyPrint.ANSI.Leijen (Doc, plain)

import Idris.AbsSyntax
import Idris.DSL
import Idris.Imports
import Idris.Delaborate
import Idris.Error
import Idris.ElabDecls
import Idris.ElabTerm hiding (namespace, params)
import Idris.Coverage
import Idris.IBC
import Idris.Unlit
import Idris.Providers

import Idris.ParseHelpers
import Idris.ParseOps
import Idris.ParseExpr
import Idris.ParseData

import Paths_idris

import Util.DynamicLinker

import Idris.Core.TT
import Idris.Core.Evaluate

import Control.Applicative
import Control.Monad
import Control.Monad.Error (throwError, catchError)
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

import System.FilePath
import System.IO

{-
 grammar shortcut notation:
    ~CHARSEQ = complement of char sequence (i.e. any character except CHARSEQ)
    RULE? = optional rule (i.e. RULE or nothing)
    RULE* = repeated rule (i.e. RULE zero or more times)
    RULE+ = repeated rule with at least one match (i.e. RULE one or more times)
    RULE! = invalid rule (i.e. rule that is not valid in context, report meaningful error in case)
    RULE{n} = rule repeated n times
-}

{- * Main grammar -}

{- | Parses module definition
      ModuleHeader ::= 'module' Identifier_t ';'?;
-}
moduleHeader :: IdrisParser [String]
moduleHeader =     try (do reserved "module"
                           i <- identifier
                           option ';' (lchar ';')
                           return (moduleName i))
               <|> try (do lchar '%'; reserved "unqualified"
                           return [])
               <|> return (moduleName "Main")
  where moduleName x = case span (/='.') x of
                           (x, "")    -> [x]
                           (x, '.':y) -> x : moduleName y

{- | Parses an import statement
  Import ::= 'import' Identifier_t ';'?;
 -}
import_ :: IdrisParser String
import_ = do reserved "import"
             id <- identifier
             option ';' (lchar ';')
             return (toPath id)
          <?> "import statement"
  where toPath f = foldl1' (</>) (Spl.splitOn "." f)

{- | Parses program source
     Prog ::= Decl* EOF;
 -}
prog :: SyntaxInfo -> IdrisParser [PDecl]
prog syn = do whiteSpace
              decls <- many (decl syn)
              notOpenBraces
              eof
              let c = (concat decls)
              return c

{- | Parses a top-level declaration
Decl ::=
    Decl'
  | Using
  | Params
  | Mutual
  | Namespace
  | Class
  | Instance
  | DSL
  | Directive
  | Provider
  | Transform
  | Import!
  ;
-}
decl :: SyntaxInfo -> IdrisParser [PDecl]
decl syn = do notEndBlock
              declBody
  where declBody :: IdrisParser [PDecl]
        declBody =     declBody'
                   <|> using_ syn
                   <|> params syn
                   <|> mutual syn
                   <|> namespace syn
                   <|> class_ syn
                   <|> instance_ syn
                   <|> do d <- dsl syn; return [d]
                   <|> directive syn
                   <|> provider syn
                   <|> transform syn
                   <|> do import_; fail "imports must be at top of file"
                   <?> "declaration"
        declBody' :: IdrisParser [PDecl]
        declBody' = do d <- decl' syn
                       i <- get
                       let d' = fmap (debindApp syn . (desugar syn i)) d
                       return [d']

{- | Parses a top-level declaration with possible syntax sugar
Decl' ::=
    Fixity
  | FunDecl'
  | Data
  | Record
  | SyntaxDecl
  ;
-}
decl' :: SyntaxInfo -> IdrisParser PDecl
decl' syn =    fixity
           <|> syntaxDecl syn
           <|> fnDecl' syn
           <|> data_ syn
           <|> record syn
           <?> "declaration"

{- | Parses a syntax extension declaration (and adds the rule to parser state)
  SyntaxDecl ::= SyntaxRule;
-}
syntaxDecl :: SyntaxInfo -> IdrisParser PDecl
syntaxDecl syn = do s <- syntaxRule syn
                    i <- get
                    let rs = syntax_rules i
                    let ns = syntax_keywords i
                    let ibc = ibc_write i
                    let ks = map show (names s)
                    put (i { syntax_rules = s : rs,
                             syntax_keywords = ks ++ ns,
                             ibc_write = IBCSyntax s : map IBCKeyword ks ++ ibc })
                    fc <- getFC
                    return (PSyntax fc s)
  where names (Rule syms _ _) = mapMaybe ename syms
        ename (Keyword n) = Just n
        ename _           = Nothing

{- | Parses a syntax extension declaration
SyntaxRuleOpts ::= 'term' | 'pattern';

SyntaxRule ::=
  SyntaxRuleOpts? 'syntax' SyntaxSym+ '=' TypeExpr Terminator;

SyntaxSym ::=   '[' Name_t ']'
             |  '{' Name_t '}'
             |  Name_t
             |  StringLiteral_t
             ;
-}
syntaxRule :: SyntaxInfo -> IdrisParser Syntax
syntaxRule syn
    = do sty <- try (do
            pushIndent
            sty <- option AnySyntax (do reserved "term"; return TermSyntax
                                  <|> do reserved "pattern"; return PatternSyntax)
            reserved "syntax"
            return sty)
         syms <- some syntaxSym
         when (all isExpr syms) $ unexpected "missing keywords in syntax rule"
         let ns = mapMaybe getName syms
         when (length ns /= length (nub ns))
            $ unexpected "repeated variable in syntax rule"
         lchar '='
         tm <- typeExpr (allowImp syn)
         terminator
         return (Rule (mkSimple syms) tm sty)
  where
    isExpr (Expr _) = True
    isExpr _ = False
    getName (Expr n) = Just n
    getName _ = Nothing
    -- Can't parse two full expressions (i.e. expressions with application) in a row
    -- so change them both to a simple expression
    mkSimple (Expr e : es) = SimpleExpr e : mkSimple' es
    mkSimple xs = mkSimple' xs

    mkSimple' (Expr e : Expr e1 : es) = SimpleExpr e : SimpleExpr e1 :
                                           mkSimple es
    mkSimple' (e : es) = e : mkSimple' es
    mkSimple' [] = []


{- | Parses a syntax symbol (either binding variable, keyword or expression)
SyntaxSym ::=   '[' Name_t ']'
             |  '{' Name_t '}'
             |  Name_t
             |  StringLiteral_t
             ;
 -}
syntaxSym :: IdrisParser SSymbol
syntaxSym =    try (do lchar '['; n <- name; lchar ']'
                       return (Expr n))
            <|> try (do lchar '{'; n <- name; lchar '}'
                        return (Binding n))
            <|> do n <- iName []
                   return (Keyword n)
            <|> do sym <- stringLiteral
                   return (Symbol sym)
            <?> "syntax symbol"

{- | Parses a function declaration with possible syntax sugar
  FunDecl ::= FunDecl';
-}
fnDecl :: SyntaxInfo -> IdrisParser [PDecl]
fnDecl syn = try (do notEndBlock
                     d <- fnDecl' syn
                     i <- get
                     let d' = fmap (desugar syn i) d
                     return [d']) <?> "function declaration"

{- Parses a function declaration
 FunDecl' ::=
  DocComment_t? FnOpts* Accessibility? FnOpts* FnName TypeSig Terminator
  | Postulate
  | Pattern
  | CAF
  ;
-}
fnDecl' :: SyntaxInfo -> IdrisParser PDecl
fnDecl' syn = checkFixity $
              do (doc, fc, opts', n, acc) <- try (do
                        doc <- option "" (docComment '|')
                        pushIndent
                        ist <- get
                        let initOpts = if default_total ist
                                          then [TotalFn]
                                          else []
                        opts <- fnOpts initOpts
                        acc <- optional accessibility
                        opts' <- fnOpts opts
                        n_in <- fnName
                        let n = expandNS syn n_in
                        fc <- getFC
                        lchar ':'
                        return (doc, fc, opts', n, acc))
                 ty <- typeExpr (allowImp syn)
                 terminator
                 addAcc n acc
                 return (PTy doc syn fc opts' n ty)
            <|> postulate syn
            <|> caf syn
            <|> pattern syn
            <?> "function declaration"
    where checkFixity :: IdrisParser PDecl -> IdrisParser PDecl
          checkFixity p = do decl <- p
                             case getName decl of
                               Nothing -> return decl
                               Just n -> do fOk <- fixityOK n
                                            unless fOk . fail $
                                              "Missing fixity declaration for " ++ show n
                                            return decl
          getName (PTy _ _ _ _ n _) = Just n
          getName _ = Nothing
          fixityOK (NS n _) = fixityOK n
          fixityOK (UN n)  | all (flip elem opChars) (str n) =
                               do fixities <- fmap idris_infixes get
                                  return . elem (str n) . map (\ (Fix _ op) -> op) $ fixities
                           | otherwise                 = return True
          fixityOK _        = return True

{- Parses function options given initial options
FnOpts ::= 'total'
  | 'partial'
  | 'implicit'
  | '%' 'assert_total'
  | '%' 'error_handler'
  | '%' 'reflection'
  | '%' 'specialise' '[' NameTimesList? ']'
  ;

NameTimes ::= FnName Natural?;

NameTimesList ::=
  NameTimes
  | NameTimes ',' NameTimesList
  ;

-}
-- FIXME: Check compatability for function options (i.e. partal/total)
fnOpts :: [FnOpt] -> IdrisParser [FnOpt]
fnOpts opts
        = do reserved "total"; fnOpts (TotalFn : opts)
      <|> do reserved "partial"; fnOpts (PartialFn : (opts \\ [TotalFn]))
      <|> do try (lchar '%' *> reserved "export"); c <- stringLiteral;
                  fnOpts (CExport c : opts)
      <|> do try (lchar '%' *> reserved "assert_total");
                  fnOpts (AssertTotal : opts)
      <|> do try (lchar '%' *> reserved "error_handler");
                 fnOpts (ErrorHandler : opts)
      <|> do try (lchar '%' *> reserved "reflection");
                  fnOpts (Reflection : opts)
      <|> do lchar '%'; reserved "specialise";
             lchar '['; ns <- sepBy nameTimes (lchar ','); lchar ']'
             fnOpts (Specialise ns : opts)
      <|> do reserved "implicit"; fnOpts (Implicit : opts)
      <|> return opts
      <?> "function modifier"
  where nameTimes :: IdrisParser (Name, Maybe Int)
        nameTimes = do n <- fnName
                       t <- option Nothing (do reds <- natural
                                               return (Just (fromInteger reds)))
                       return (n, t)

{- | Parses a postulate

Postulate ::=
  DocComment_t? 'postulate' FnOpts* Accesibility? FnOpts* FnName TypeSig Terminator
  ;
-}
postulate :: SyntaxInfo -> IdrisParser PDecl
postulate syn = do doc <- try $ do doc <- option "" (docComment '|')
                                   pushIndent
                                   reserved "postulate"
                                   return doc
                   ist <- get
                   let initOpts = if default_total ist
                                     then [TotalFn]
                                     else []
                   opts <- fnOpts initOpts
                   acc <- optional accessibility
                   opts' <- fnOpts opts
                   n_in <- fnName
                   let n = expandNS syn n_in
                   lchar ':'
                   ty <- typeExpr (allowImp syn)
                   fc <- getFC
                   terminator
                   addAcc n acc
                   return (PPostulate doc syn fc opts' n ty)
                 <?> "postulate"

{- | Parses a using declaration

Using ::=
  'using' '(' UsingDeclList ')' OpenBlock Decl* CloseBlock
  ;
 -}
using_ :: SyntaxInfo -> IdrisParser [PDecl]
using_ syn =
    do reserved "using"; lchar '('; ns <- usingDeclList syn; lchar ')'
       openBlock
       let uvars = using syn
       ds <- many (decl (syn { using = uvars ++ ns }))
       closeBlock
       return (concat ds)
    <?> "using declaration"

{- | Parses a parameters declaration

Params ::=
  'parameters' '(' TypeDeclList ')' OpenBlock Decl* CloseBlock
  ;
 -}
params :: SyntaxInfo -> IdrisParser [PDecl]
params syn =
    do reserved "parameters"; lchar '('; ns <- typeDeclList syn; lchar ')'
       openBlock
       let pvars = syn_params syn
       ds <- many (decl syn { syn_params = pvars ++ ns })
       closeBlock
       fc <- getFC
       return [PParams fc ns (concat ds)]
    <?> "parameters declaration"

{- | Parses a mutual declaration (for mutually recursive functions)

Mutual ::=
  'mutual' OpenBlock Decl* CloseBlock
  ;
-}
mutual :: SyntaxInfo -> IdrisParser [PDecl]
mutual syn =
    do reserved "mutual"
       openBlock
       let pvars = syn_params syn
       ds <- many (decl syn)
       closeBlock
       fc <- getFC
       return [PMutual fc (concat ds)]
    <?> "mutual block"

{- | Parses a namespace declaration

Namespace ::=
  'namespace' identifier OpenBlock Decl+ CloseBlock
  ;
-}
namespace :: SyntaxInfo -> IdrisParser [PDecl]
namespace syn =
    do reserved "namespace"; n <- identifier;
       openBlock
       ds <- some (decl syn { syn_namespace = n : syn_namespace syn })
       closeBlock
       return [PNamespace n (concat ds)]
     <?> "namespace declaration"

{- |Parses a methods block (for instances)
  InstanceBlock ::= 'where' OpenBlock FnDecl* CloseBlock
 -}
instanceBlock :: SyntaxInfo -> IdrisParser [PDecl]
instanceBlock syn = do reserved "where"
                       openBlock
                       ds <- many (fnDecl syn)
                       closeBlock
                       return (concat ds)
                    <?> "instance block"

{- |Parses a methods and instances block (for type classes)

MethodOrInstance ::=
   FnDecl
   | Instance
   ;

ClassBlock ::=
  'where' OpenBlock MethodOrInstance* CloseBlock
  ;
-}
classBlock :: SyntaxInfo -> IdrisParser [PDecl]
classBlock syn = do reserved "where"
                    openBlock
                    ds <- many ((notEndBlock >> instance_ syn) <|> fnDecl syn)
                    closeBlock
                    return (concat ds)
                 <?> "class block"

{- |Parses a type class declaration

ClassArgument ::=
   Name
   | '(' Name ':' Expr ')'
   ;

Class ::=
  DocComment_t? Accessibility? 'class' ConstraintList? Name ClassArgument* ClassBlock?
  ;
-}
class_ :: SyntaxInfo -> IdrisParser [PDecl]
class_ syn = do (doc, acc) <- try (do
                  doc <- option "" (docComment '|')
                  acc <- optional accessibility
                  return (doc, acc))
                reserved "class"; fc <- getFC; cons <- constraintList syn; n_in <- name
                let n = expandNS syn n_in
                cs <- many carg
                ds <- option [] (classBlock syn)
                accData acc n (concatMap declared ds)
                return [PClass doc syn fc cons n cs ds]
             <?> "type-class declaration"
  where
    carg :: IdrisParser (Name, PTerm)
    carg = do lchar '('; i <- name; lchar ':'; ty <- expr syn; lchar ')'
              return (i, ty)
       <|> do i <- name;
              return (i, PType)

{- |Parses a type class instance declaration

  Instance ::=
    'instance' InstanceName? ConstraintList? Name SimpleExpr* InstanceBlock?
    ;

  InstanceName ::= '[' Name ']';
-}
instance_ :: SyntaxInfo -> IdrisParser [PDecl]
instance_ syn = do reserved "instance"; fc <- getFC
                   en <- optional instanceName
                   cs <- constraintList syn
                   cn <- name
                   args <- many (simpleExpr syn)
                   let sc = PApp fc (PRef fc cn) (map pexp args)
                   let t = bindList (PPi constraint) (map (\x -> (sMN 0 "constraint", x)) cs) sc
                   ds <- option [] (instanceBlock syn)
                   return [PInstance syn fc cs cn args t en ds]
                 <?> "instance declaration"
  where instanceName :: IdrisParser Name
        instanceName = do lchar '['; n_in <- fnName; lchar ']'
                          let n = expandNS syn n_in
                          return n
                       <?> "instance name"


{- | Parses a using declaration list
UsingDeclList ::=
  UsingDeclList'
  | NameList TypeSig
  ;

UsingDeclList' ::=
  UsingDecl
  | UsingDecl ',' UsingDeclList'
  ;

NameList ::=
  Name
  | Name ',' NameList
  ;
-}
usingDeclList :: SyntaxInfo -> IdrisParser [Using]
usingDeclList syn
               = try (sepBy1 (usingDecl syn) (lchar ','))
             <|> do ns <- sepBy1 name (lchar ',')
                    lchar ':'
                    t <- typeExpr (disallowImp syn)
                    return (map (\x -> UImplicit x t) ns)
             <?> "using declaration list"

{- |Parses a using declaration
UsingDecl ::=
  FnName TypeSig
  | FnName FnName+
  ;
-}
usingDecl :: SyntaxInfo -> IdrisParser Using
usingDecl syn = try (do x <- fnName
                        lchar ':'
                        t <- typeExpr (disallowImp syn)
                        return (UImplicit x t))
            <|> do c <- fnName
                   xs <- some fnName
                   return (UConstraint c xs)
            <?> "using declaration"

{- | Parse a clause with patterns
Pattern ::= Clause;
-}
pattern :: SyntaxInfo -> IdrisParser PDecl
pattern syn = do fc <- getFC
                 clause <- clause syn
                 return (PClauses fc [] (sMN 2 "_") [clause]) -- collect together later
              <?> "pattern"

{- | Parse a constant applicative form declaration
  CAF ::= 'let' FnName '=' Expr Terminator;
-}
caf :: SyntaxInfo -> IdrisParser PDecl
caf syn = do reserved "let"
             n_in <- fnName; let n = expandNS syn n_in
             lchar '='
             t <- expr syn
             terminator
             fc <- getFC
             return (PCAF fc n t)
           <?> "constant applicative form declaration"

{- | Parse an argument expression
  ArgExpr ::= HSimpleExpr | {- In Pattern External (User-defined) Expression -};
-}
argExpr :: SyntaxInfo -> IdrisParser PTerm
argExpr syn = let syn' = syn { inPattern = True } in
                  try (hsimpleExpr syn') <|> simpleExternalExpr syn'
              <?> "argument expression"

{- | Parse a right hand side of a function
RHS ::= '='            Expr
     |  '?='  RHSName? Expr
     |  'impossible'
     ;

RHSName ::= '{' FnName '}';
-}
rhs :: SyntaxInfo -> Name -> IdrisParser PTerm
rhs syn n = do lchar '='; expr syn
        <|> do symbol "?=";
               name <- option n' (do symbol "{"; n <- fnName; symbol "}";
                                     return n)
               r <- expr syn
               return (addLet name r)
        <|> do reserved "impossible"; return PImpossible
        <?> "function right hand side"
  where mkN :: Name -> Name
        mkN (UN x)   = sUN (str x++"_lemma_1")
        mkN (NS x n) = NS (mkN x) n
        n' :: Name
        n' = mkN n
        addLet :: Name -> PTerm -> PTerm
        addLet nm (PLet n ty val r) = PLet n ty val (addLet nm r)
        addLet nm (PCase fc t cs) = PCase fc t (map addLetC cs)
          where addLetC (l, r) = (l, addLet nm r)
        addLet nm r = (PLet (sUN "value") Placeholder r (PMetavar nm))

{- |Parses a function clause
RHSOrWithBlock ::= RHS WhereOrTerminator
               | 'with' SimpleExpr OpenBlock FnDecl+ CloseBlock
               ;
Clause ::=                                                               WExpr+ RHSOrWithBlock
       |   SimpleExpr '<=='  FnName                                             RHS WhereOrTerminator
       |   ArgExpr Operator ArgExpr                                      WExpr* RHSOrWithBlock {- Except "=" and "?=" operators to avoid ambiguity -}
       |                     FnName ConstraintArg* ImplicitOrArgExpr*    WExpr* RHSOrWithBlock
       ;
ImplicitOrArgExpr ::= ImplicitArg | ArgExpr;
WhereOrTerminator ::= WhereBlock | Terminator;
-}
clause :: SyntaxInfo -> IdrisParser PClause
clause syn
         = do wargs <- try (do pushIndent; some (wExpr syn))
              fc <- getFC
              ist <- get
              n <- case lastParse ist of
                        Just t -> return t
                        Nothing -> fail "Invalid clause"
              (do r <- rhs syn n
                  let ctxt = tt_ctxt ist
                  let wsyn = syn { syn_namespace = [] }
                  (wheres, nmap) <- choice [do x <- whereBlock n wsyn
                                               popIndent
                                               return x,
                                            do terminator
                                               return ([], [])]
                  return $ PClauseR fc wargs r wheres) <|> (do
                  popIndent
                  reserved "with"
                  wval <- simpleExpr syn
                  openBlock
                  ds <- some $ fnDecl syn
                  let withs = concat ds
                  closeBlock
                  return $ PWithR fc wargs wval withs)
       <|> do ty <- try (do pushIndent
                            ty <- simpleExpr syn
                            symbol "<=="
                            return ty)
              fc <- getFC
              n_in <- fnName; let n = expandNS syn n_in
              r <- rhs syn n
              ist <- get
              let ctxt = tt_ctxt ist
              let wsyn = syn { syn_namespace = [] }
              (wheres, nmap) <- choice [do x <- whereBlock n wsyn
                                           popIndent
                                           return x,
                                        do terminator
                                           return ([], [])]
              let capp = PLet (sMN 0 "match")
                              ty
                              (PMatchApp fc n)
                              (PRef fc (sMN 0 "match"))
              ist <- get
              put (ist { lastParse = Just n })
              return $ PClause fc n capp [] r wheres
       <|> do (l, op) <- try (do
                pushIndent
                l <- argExpr syn
                op <- operator
                when (op == "=" || op == "?=" ) $
                     fail "infix clause definition with \"=\" and \"?=\" not supported "
                return (l, op))
              let n = expandNS syn (sUN op)
              r <- argExpr syn
              fc <- getFC
              wargs <- many (wExpr syn)
              (do rs <- rhs syn n
                  let wsyn = syn { syn_namespace = [] }
                  (wheres, nmap) <- choice [do x <- whereBlock n wsyn
                                               popIndent
                                               return x,
                                            do terminator
                                               return ([], [])]
                  ist <- get
                  let capp = PApp fc (PRef fc n) [pexp l, pexp r]
                  put (ist { lastParse = Just n })
                  return $ PClause fc n capp wargs rs wheres) <|> (do
                   popIndent
                   reserved "with"
                   lchar '(' <?> "parenthesized expression"
                   wval <- bracketed syn
                   openBlock
                   ds <- some $ fnDecl syn
                   closeBlock
                   ist <- get
                   let capp = PApp fc (PRef fc n) [pexp l, pexp r]
                   let withs = map (fillLHSD n capp wargs) $ concat ds
                   put (ist { lastParse = Just n })
                   return $ PWith fc n capp wargs wval withs)
       <|> do pushIndent
              n_in <- fnName; let n = expandNS syn n_in
              cargs <- many (constraintArg syn)
              fc <- getFC
              args <- many (try (implicitArg (syn { inPattern = True } ))
                            <|> (fmap pexp (argExpr syn)))
              wargs <- many (wExpr syn)
              let capp = PApp fc (PRef fc n)
                           (cargs ++ args)
              (do r <- rhs syn n
                  ist <- get
                  let ctxt = tt_ctxt ist
                  let wsyn = syn { syn_namespace = [] }
                  (wheres, nmap) <- choice [do x <- whereBlock n wsyn
                                               popIndent
                                               return x,
                                            do terminator
                                               return ([], [])]
                  ist <- get
                  put (ist { lastParse = Just n })
                  return $ PClause fc n capp wargs r wheres) <|> (do
                   reserved "with"
                   ist <- get
                   put (ist { lastParse = Just n })
                   lchar '(' <?> "parenthesized expression"
                   wval <- bracketed syn
                   openBlock
                   ds <- some $ fnDecl syn
                   let withs = map (fillLHSD n capp wargs) $ concat ds
                   closeBlock
                   popIndent
                   return $ PWith fc n capp wargs wval withs)
      <?> "function clause"
  where
    fillLHS :: Name -> PTerm -> [PTerm] -> PClause -> PClause
    fillLHS n capp owargs (PClauseR fc wargs v ws)
       = PClause fc n capp (owargs ++ wargs) v ws
    fillLHS n capp owargs (PWithR fc wargs v ws)
       = PWith fc n capp (owargs ++ wargs) v
            (map (fillLHSD n capp (owargs ++ wargs)) ws)
    fillLHS _ _ _ c = c

    fillLHSD :: Name -> PTerm -> [PTerm] -> PDecl -> PDecl
    fillLHSD n c a (PClauses fc o fn cs) = PClauses fc o fn (map (fillLHS n c a) cs)
    fillLHSD n c a x = x

{- |Parses with pattern
 WExpr ::= '|' Expr';
-}
wExpr :: SyntaxInfo -> IdrisParser PTerm
wExpr syn = do lchar '|'
               expr' syn
            <?> "with pattern"

{- |Parses a where block
WhereBlock ::= 'where' OpenBlock Decl+ CloseBlock;
 -}
whereBlock :: Name -> SyntaxInfo -> IdrisParser ([PDecl], [(Name, Name)])
whereBlock n syn
    = do reserved "where"
         ds <- indentedBlock1 (decl syn)
         let dns = concatMap (concatMap declared) ds
         return (concat ds, map (\x -> (x, decoration syn x)) dns)
      <?> "where block"

{- |Parses a code generation target language name
Codegen ::= 'C'
        |   'Java'
        |   'JavaScript'
        |   'Node'
        |   'LLVM'
        |   'Bytecode'
        ;
-}
codegen_ :: IdrisParser Codegen
codegen_ = do reserved "C"; return ViaC
       <|> do reserved "Java"; return ViaJava
       <|> do reserved "JavaScript"; return ViaJavaScript
       <|> do reserved "Node"; return ViaNode
       <|> do reserved "LLVM"; return ViaLLVM
       <|> do reserved "Bytecode"; return Bytecode
       <?> "code generation language"

{- |Parses a compiler directive
StringList ::=
  String
  | String ',' StringList
  ;

Directive ::= '%' Directive';

Directive' ::= 'lib'      CodeGen String_t
           |   'link'     CodeGen String_t
           |   'flag'     CodeGen String_t
           |   'include'  CodeGen String_t
           |   'hide'     Name
           |   'freeze'   Name
           |   'access'   Accessibility
           |   'default'  Totality
           |   'logging'  Natural
           |   'dynamic'  StringList
           |   'name'     Name NameList
           |   'language' 'TypeProviders'
           |   'language' 'ErrorReflection'
           ;
-}
directive :: SyntaxInfo -> IdrisParser [PDecl]
directive syn = do try (lchar '%' *> reserved "lib"); cgn <- codegen_; lib <- stringLiteral;
                   return [PDirective (do addLib cgn lib
                                          addIBC (IBCLib cgn lib))]
             <|> do try (lchar '%' *> reserved "link"); cgn <- codegen_; obj <- stringLiteral;
                    return [PDirective (do dirs <- allImportDirs
                                           o <- liftIO $ findInPath dirs obj
                                           addIBC (IBCObj cgn obj) -- just name, search on loading ibc
                                           addObjectFile cgn o)]
             <|> do try (lchar '%' *> reserved "flag"); cgn <- codegen_;
                    flag <- stringLiteral
                    return [PDirective (do addIBC (IBCCGFlag cgn flag)
                                           addFlag cgn flag)]
             <|> do try (lchar '%' *> reserved "include"); cgn <- codegen_; hdr <- stringLiteral;
                    return [PDirective (do addHdr cgn hdr
                                           addIBC (IBCHeader cgn hdr))]
             <|> do try (lchar '%' *> reserved "hide"); n <- fnName
                    return [PDirective (do setAccessibility n Hidden
                                           addIBC (IBCAccess n Hidden))]
             <|> do try (lchar '%' *> reserved "freeze"); n <- iName []
                    return [PDirective (do setAccessibility n Frozen
                                           addIBC (IBCAccess n Frozen))]
             <|> do try (lchar '%' *> reserved "access"); acc <- accessibility
                    return [PDirective (do i <- get
                                           put(i { default_access = acc }))]
             <|> do try (lchar '%' *> reserved "default"); tot <- totality
                    i <- get
                    put (i { default_total = tot } )
                    return [PDirective (do i <- get
                                           put(i { default_total = tot }))]
             <|> do try (lchar '%' *> reserved "logging"); i <- natural;
                    return [PDirective (setLogLevel (fromInteger i))]
             <|> do try (lchar '%' *> reserved "dynamic"); libs <- sepBy1 stringLiteral (lchar ',');
                    return [PDirective (do added <- addDyLib libs
                                           case added of
                                             Left lib -> addIBC (IBCDyLib (lib_name lib))
                                             Right msg ->
                                                 fail $ msg)]
             <|> do try (lchar '%' *> reserved "name")
                    ty <- iName []
                    ns <- sepBy1 name (lchar ',')
                    return [PDirective 
                               (do i <- getIState
                                   ty' <- case lookupCtxtName ty (idris_implicits i) of
                                             [(tyn, _)] -> return tyn
                                             [] -> throwError (NoSuchVariable ty)
                                             tyns -> throwError (CantResolveAlts (map show (map fst tyns)))
                                   mapM_ (addNameHint ty') ns
                                   mapM_ (\n -> addIBC (IBCNameHint (ty', n))) ns)] 
             <|> do try (lchar '%' *> reserved "language"); ext <- pLangExt;
                    return [PDirective (addLangExt ext)]
             <?> "directive"

pLangExt :: IdrisParser LanguageExt
pLangExt = (reserved "TypeProviders" >> return TypeProviders)
       <|> (reserved "ErrorReflection" >> return ErrorReflection)

{- | Parses a totality
Totality ::= 'partial' | 'total'
-}
totality :: IdrisParser Bool
totality
        = do reserved "total";   return True
      <|> do reserved "partial"; return False

{- | Parses a type provider
Provider ::= '%' 'provide' '(' FnName TypeSig ')' 'with' Expr;
 -}
provider :: SyntaxInfo -> IdrisParser [PDecl]
provider syn = do try (lchar '%' *> reserved "provide");
                  lchar '('; n <- fnName; lchar ':'; t <- typeExpr syn; lchar ')'
                  fc <- getFC
                  reserved "with"
                  e <- expr syn
                  return  [PProvider syn fc n t e]
               <?> "type provider"

{- | Parses a transform
Transform ::= '%' 'transform' Expr '==>' Expr
-}
transform :: SyntaxInfo -> IdrisParser [PDecl]
transform syn = do try (lchar '%' *> reserved "transform")
                    -- leave it unchecked, until we work out what this should
                    -- actually mean...
--                     safety <- option True (do reserved "unsafe"
--                                               return False)
                   l <- expr syn
                   fc <- getFC
                   symbol "==>"
                   r <- expr syn
                   return [PTransform fc False l r]
                <?> "transform"


{- * Loading and parsing -}
{- | Parses an expression from input -}
parseExpr :: IState -> String -> Result PTerm
parseExpr st = runparser (fullExpr defaultSyntax) st "(input)"

{- | Parses a tactic from input -}
parseTactic :: IState -> String -> Result PTactic
parseTactic st = runparser (fullTactic defaultSyntax) st "(input)"

-- | Parse module header and imports
parseImports :: FilePath -> String -> Idris ([String], [String], Maybe Delta)
parseImports fname input
    = do i <- getIState
         case parseString (runInnerParser (evalStateT imports i)) (Directed (UTF8.fromString fname) 0 0 0 0) input of
              Failure err    -> fail (show err)
              Success (x, i) -> do -- Discard state updates (there should be
                                   -- none anyway)
                                   return x
  where imports :: IdrisParser (([String], [String], Maybe Delta), IState)
        imports = do whiteSpace
                     mname <- moduleHeader
                     ps    <- many import_
                     mrk   <- mark
                     isEof <- lookAheadMatches eof
                     let mrk' = if isEof
                                   then Nothing
                                   else Just mrk
                     i     <- get
                     return ((mname, ps, mrk'), i)

-- | There should be a better way of doing this...
findFC :: Doc -> (FC, String)
findFC x = let s = show (plain x) in
             case span (/= ':') s of
               (failname, ':':rest) -> case span isDigit rest of
                 (line, ':':rest') -> case span isDigit rest' of
                   (col, ':':msg) -> (FC failname (read line) (read col), msg)

-- | A program is a list of declarations, possibly with associated
-- documentation strings.
parseProg :: SyntaxInfo -> FilePath -> String -> Maybe Delta ->
             Idris [PDecl]
parseProg syn fname input mrk
    = do i <- getIState
         case runparser mainProg i fname input of
            Failure doc     -> do -- FIXME: Get error location from trifecta
                                  -- this can't be the solution!
                                  let (fc, msg) = findFC doc
                                  i <- getIState
                                  case idris_outputmode i of
                                    RawOutput -> ihputStrLn (idris_outh i) (show doc)
                                    IdeSlave n -> ihWarn (idris_outh i) fc msg
                                  putIState (i { errLine = Just (fc_line fc) }) -- Just errl })
                                  return []
            Success (x, i)  -> do putIState i
                                  return $ collect x
  where mainProg :: IdrisParser ([PDecl], IState)
        mainProg = case mrk of
                        Nothing -> do i <- get; return ([], i)
                        Just mrk -> do
                          release mrk
                          ds <- prog syn
                          i' <- get
                          return (ds, i')

{- | Load idris module and show error if something wrong happens -}
loadModule :: Handle -> FilePath -> Idris String
loadModule outh f
   = idrisCatch (loadModule' outh f)
                (\e -> do setErrLine (getErrLine e)
                          ist <- getIState
                          msg <- showErr e
                          ihputStrLn outh msg
                          return "")

{- | Load idris module -}
loadModule' :: Handle -> FilePath -> Idris String
loadModule' outh f
   = do i <- getIState
        let file = takeWhile (/= ' ') f
        ibcsd <- valIBCSubDir i
        ids <- allImportDirs
        fp <- liftIO $ findImport ids ibcsd file
        if file `elem` imported i
          then iLOG $ "Already read " ++ file
          else do putIState (i { imported = file : imported i })
                  case fp of
                    IDR fn  -> loadSource outh False fn
                    LIDR fn -> loadSource outh True  fn
                    IBC fn src ->
                      idrisCatch (loadIBC fn)
                                 (\c -> do iLOG $ fn ++ " failed " ++ pshow i c
                                           case src of
                                             IDR sfn -> loadSource outh False sfn
                                             LIDR sfn -> loadSource outh True sfn)
        let (dir, fh) = splitFileName file
        return (dropExtension fh)


{- | Load idris code from file -}
loadFromIFile :: Handle -> IFileType -> Idris ()
loadFromIFile h i@(IBC fn src)
   = do iLOG $ "Skipping " ++ getSrcFile i
        idrisCatch (loadIBC fn)
                (\err -> ierror $ LoadingFailed fn err)
  where
    getSrcFile (IDR fn) = fn
    getSrcFile (LIDR fn) = fn
    getSrcFile (IBC f src) = getSrcFile src

loadFromIFile h (IDR fn) = loadSource' h False fn
loadFromIFile h (LIDR fn) = loadSource' h True fn

{-| Load idris source code and show error if something wrong happens -}
loadSource' :: Handle -> Bool -> FilePath -> Idris ()
loadSource' h lidr r
   = idrisCatch (loadSource h lidr r)
                (\e -> do setErrLine (getErrLine e)
                          msg <- showErr e
                          ihputStrLn h msg)

{- | Load Idris source code-}
loadSource :: Handle -> Bool -> FilePath -> Idris ()
loadSource h lidr f
             = do iLOG ("Reading " ++ f)
                  i <- getIState
                  let def_total = default_total i
                  file_in <- runIO $ readFile f
                  file <- if lidr then tclift $ unlit f file_in else return file_in
                  (mname, modules, pos) <- parseImports f file
                  i <- getIState
                  putIState (i { default_access = Hidden })
                  clearIBC -- start a new .ibc file
                  mapM_ (addIBC . IBCImport) modules
                  ds' <- parseProg (defaultSyntax {syn_namespace = reverse mname })
                                   f file pos
                  unless (null ds') $ do
                    let ds = namespaces mname ds'
                    logLvl 3 (showDecls True ds)
                    i <- getIState
                    logLvl 10 (show (toAlist (idris_implicits i)))
                    logLvl 3 (show (idris_infixes i))
                    -- Now add all the declarations to the context
                    v <- verbose
                    when v $ ihputStrLn h $ "Type checking " ++ f
                    -- we totality check after every Mutual block, so if
                    -- anything is a single definition, wrap it in a
                    -- mutual block on its own
                    elabDecls toplevel (map toMutual ds)
                    i <- getIState
                    -- simplify every definition do give the totality checker
                    -- a better chance
                    mapM_ (\n -> do logLvl 5 $ "Simplifying " ++ show n
                                    updateContext (simplifyCasedef n))
                             (map snd (idris_totcheck i))
                    -- build size change graph from simplified definitions
                    iLOG "Totality checking"
                    i <- getIState
                    mapM_ buildSCG (idris_totcheck i)
                    mapM_ checkDeclTotality (idris_totcheck i)

                    -- Redo totality check for deferred names
                    let deftots = idris_defertotcheck i
                    iLOG $ "Totality checking " ++ show deftots
                    mapM_ (\x -> do tot <- getTotality x
                                    case tot of
                                         Total _ -> setTotality x Unchecked
                                         _ -> return ()) (map snd deftots)
                    mapM_ buildSCG deftots
                    mapM_ checkDeclTotality deftots

                    iLOG ("Finished " ++ f)
                    ibcsd <- valIBCSubDir i
                    iLOG "Universe checking"
                    iucheck
                    let ibc = ibcPathNoFallback ibcsd f
                    i <- getIState
                    addHides (hide_list i)
                    ok <- noErrors
                    when ok $
                      idrisCatch (do writeIBC f ibc; clearIBC)
                                 (\c -> return ()) -- failure is harmless
                    i <- getIState
                    putIState (i { default_total = def_total,
                                   hide_list = [] })
                    return ()
                  return ()
  where
    namespaces :: [String] -> [PDecl] -> [PDecl]
    namespaces []     ds = ds
    namespaces (x:xs) ds = [PNamespace x (namespaces xs ds)]

    toMutual :: PDecl -> PDecl
    toMutual m@(PMutual _ d) = m
    toMutual (PNamespace x ds) = PNamespace x (map toMutual ds)
    toMutual x = let r = PMutual (fileFC "single mutual") [x] in
                 case x of
                   PClauses _ _ _ _ -> r
                   PClass _ _ _ _ _ _ _ -> r
                   PInstance _ _ _ _ _ _ _ _ -> r
                   _ -> x

{- | Adds names to hide list -}
addHides :: [(Name, Maybe Accessibility)] -> Idris ()
addHides xs = do i <- getIState
                 let defh = default_access i
                 let (hs, as) = partition isNothing xs
                 unless (null as) $
                   mapM_ doHide
                     (map (\ (n, _) -> (n, defh)) hs ++
                       map (\ (n, Just a) -> (n, a)) as)
  where isNothing (_, Nothing) = True
        isNothing _            = False

        doHide (n, a) = do setAccessibility n a
                           addIBC (IBCAccess n a)

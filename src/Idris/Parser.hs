{-|
Module      : Idris.Parser
Description : Idris' parser.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE ConstraintKinds, GeneralizedNewtypeDeriving, PatternGuards #-}
{-# OPTIONS_GHC -O0 #-}
module Idris.Parser(module Idris.Parser,
                    module Idris.Parser.Expr,
                    module Idris.Parser.Data,
                    module Idris.Parser.Helpers,
                    module Idris.Parser.Ops) where

import Idris.AbsSyntax hiding (namespace, params)
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Coverage
import Idris.Delaborate
import Idris.Docstrings hiding (Unchecked)
import Idris.DSL
import Idris.Elab.Term
import Idris.Elab.Value
import Idris.ElabDecls
import Idris.Error
import Idris.IBC
import Idris.Imports
import Idris.Output
import Idris.Parser.Data
import Idris.Parser.Expr
import Idris.Parser.Helpers
import Idris.Parser.Ops
import Idris.Providers
import Idris.Termination
import Idris.Unlit

import Util.DynamicLinker
import qualified Util.Pretty as P
import Util.System (readSource, writeSource)

import Paths_idris

import Prelude hiding (pi)

import Control.Applicative hiding (Const)
import Control.Monad
import Control.Monad.State.Strict
import qualified Data.ByteString.UTF8 as UTF8
import Data.Char
import Data.Foldable (asum)
import Data.Function
import Data.Generics.Uniplate.Data (descendM)
import qualified Data.HashSet as HS
import Data.List
import qualified Data.List.Split as Spl
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.Ord
import qualified Data.Set as S
import qualified Data.Text as T
import Debug.Trace
import qualified System.Directory as Dir (makeAbsolute)
import System.FilePath
import System.IO
import qualified Text.Parser.Char as Chr
import Text.Parser.Expression
import Text.Parser.LookAhead
import qualified Text.Parser.Token as Tok
import qualified Text.Parser.Token.Highlight as Hi
import Text.PrettyPrint.ANSI.Leijen (Doc, plain)
import qualified Text.PrettyPrint.ANSI.Leijen as ANSI
import Text.Trifecta hiding (Err, char, charLiteral, natural, span, string,
                      stringLiteral, symbol, whiteSpace)
import Text.Trifecta.Delta

{-
@
 grammar shortcut notation:
    ~CHARSEQ = complement of char sequence (i.e. any character except CHARSEQ)
    RULE? = optional rule (i.e. RULE or nothing)
    RULE* = repeated rule (i.e. RULE zero or more times)
    RULE+ = repeated rule with at least one match (i.e. RULE one or more times)
    RULE! = invalid rule (i.e. rule that is not valid in context, report meaningful error in case)
    RULE{n} = rule repeated n times
@
-}

{- * Main grammar -}

{-| Parses module definition

@
      ModuleHeader ::= DocComment_t? 'module' Identifier_t ';'?;
@
-}
moduleHeader :: IdrisParser (Maybe (Docstring ()), [String], [(FC, OutputAnnotation)])
moduleHeader =     try (do docs <- optional docComment
                           noArgs docs
                           reservedHL "module"
                           (i, ifc) <- identifier
                           option ';' (lchar ';')
                           let modName = moduleName i
                           return (fmap fst docs,
                                   modName,
                                   [(ifc, AnnNamespace (map T.pack modName) Nothing)]))
               <|> try (do lchar '%'; reserved "unqualified"
                           return (Nothing, [], []))
               <|> return (Nothing, moduleName "Main", [])
  where moduleName x = case span (/='.') x of
                           (x, "")    -> [x]
                           (x, '.':y) -> x : moduleName y
        noArgs (Just (_, args)) | not (null args) = fail "Modules do not take arguments"
        noArgs _ = return ()

data ImportInfo = ImportInfo { import_reexport :: Bool
                             , import_path :: FilePath
                             , import_rename :: Maybe (String, FC)
                             , import_namespace :: [T.Text]
                             , import_location :: FC
                             , import_modname_location :: FC
                             }

{-| Parses an import statement

@
  Import ::= 'import' Identifier_t ';'?;
@
 -}
import_ :: IdrisParser ImportInfo
import_ = do fc <- getFC
             reservedHL "import"
             reexport <- option False (do reservedHL "public"
                                          return True)
             (id, idfc) <- identifier
             newName <- optional (do reservedHL "as"
                                     identifier)
             option ';' (lchar ';')
             return $ ImportInfo reexport (toPath id)
                        (fmap (\(n, fc) -> (toPath n, fc)) newName)
                        (map T.pack $ ns id) fc idfc
          <?> "import statement"
  where ns = Spl.splitOn "."
        toPath = foldl1' (</>) . ns

{-| Parses program source

@
     Prog ::= Decl* EOF;
@
 -}
prog :: SyntaxInfo -> IdrisParser [PDecl]
prog syn = do whiteSpace
              decls <- many (decl syn)
              let c = concat decls
              case maxline syn of
                   Nothing -> do notOpenBraces; eof
                   _ -> return ()
              ist <- get
              fc <- getFC
              put ist { idris_parsedSpan = Just (FC (fc_fname fc) (0,0) (fc_end fc)),
                        ibc_write = IBCParsedRegion fc : ibc_write ist }
              return c

{-| Parses a top-level declaration

@
Decl ::=
    Decl'
  | Using
  | Params
  | Mutual
  | Namespace
  | Interface
  | Implementation
  | DSL
  | Directive
  | Provider
  | Transform
  | Import!
  | RunElabDecl
  ;
@
-}
decl :: SyntaxInfo -> IdrisParser [PDecl]
decl syn = try (externalDecl syn)
           <|> internalDecl syn
           <?> "declaration"

internalDecl :: SyntaxInfo -> IdrisParser [PDecl]
internalDecl syn
         = do fc <- getFC
              -- if we're after maxline, stop at the next type declaration
              -- (so we get all cases of a definition to preserve totality
              -- results, in particular).
              let continue = case maxline syn of
                                Nothing -> True
                                Just l -> if fst (fc_end fc) > l
                                             then mut_nesting syn /= 0
                                             else True
              -- What I'd really like to do here is explicitly save the
              -- current state, then if reading ahead finds we've passed
              -- the end of the definition, reset the state. But I've lost
              -- patience with trying to find out how to do that from the
              -- trifecta docs, so this does the job instead.
              if continue then
                 do notEndBlock
                    declBody continue
                else try (do notEndBlock
                             declBody continue)
                     <|> fail "End of readable input"
  where declBody :: Bool -> IdrisParser [PDecl]
        declBody b =
                   try (implementation True syn)
                   <|> try (openInterface syn)
                   <|> declBody' b
                   <|> using_ syn
                   <|> params syn
                   <|> mutual syn
                   <|> namespace syn
                   <|> interface_ syn
                   <|> do d <- dsl syn; return [d]
                   <|> directive syn
                   <|> provider syn
                   <|> transform syn
                   <|> do import_; fail "imports must be at top of file"
                   <?> "declaration"
        declBody' :: Bool -> IdrisParser [PDecl]
        declBody' cont = do d <- decl' syn
                            i <- get
                            let d' = fmap (debindApp syn . (desugar syn i)) d
                            if continue cont d'
                               then return [d']
                               else fail "End of readable input"

        -- Keep going while we're still parsing clauses
        continue False (PClauses _ _ _ _) = True
        continue c _ = c

{-| Parses a top-level declaration with possible syntax sugar

@
Decl' ::=
    Fixity
  | FunDecl'
  | Data
  | Record
  | SyntaxDecl
  ;
@
-}
decl' :: SyntaxInfo -> IdrisParser PDecl
decl' syn =    fixity
           <|> syntaxDecl syn
           <|> fnDecl' syn
           <|> data_ syn
           <|> record syn
           <|> runElabDecl syn
           <?> "declaration"

externalDecl :: SyntaxInfo -> IdrisParser [PDecl]
externalDecl syn = do i <- get
                      notEndBlock
                      FC fn start _ <- getFC
                      decls <- declExtensions syn (syntaxRulesList $ syntax_rules i)
                      FC _ _ end <- getFC
                      let outerFC = FC fn start end
                      return $ map (mapPDeclFC (fixFC outerFC)
                                               (fixFCH fn outerFC))
                                   decls
  where
    -- | Fix non-highlighting FCs to prevent spurious error location reports
    fixFC :: FC -> FC -> FC
    fixFC outer inner | inner `fcIn` outer = inner
                      | otherwise          = outer
    -- | Fix highlighting FCs by obliterating them, to avoid spurious highlights
    fixFCH fn outer inner | inner `fcIn` outer = inner
                          | otherwise          = FileFC fn

declExtensions :: SyntaxInfo -> [Syntax] -> IdrisParser [PDecl]
declExtensions syn rules = declExtension syn [] (filter isDeclRule rules)
                           <?> "user-defined declaration"
   where
     isDeclRule (DeclRule _ _) = True
     isDeclRule _ = False

declExtension :: SyntaxInfo -> [Maybe (Name, SynMatch)] -> [Syntax]
                 -> IdrisParser [PDecl]
declExtension syn ns rules =
  choice $ flip map (groupBy (ruleGroup `on` syntaxSymbols) rules) $ \rs ->
    case head rs of -- can never be []
      DeclRule (symb:_) _ -> try $ do
        n <- extSymbol symb
        declExtension syn (n : ns) [DeclRule ss t | (DeclRule (_:ss) t) <- rs]
      -- If we have more than one Rule in this bucket, our grammar is
      -- nondeterministic.
      DeclRule [] dec -> let r = map (update (mapMaybe id ns)) dec in
                             return r

  where
    update :: [(Name, SynMatch)] -> PDecl -> PDecl
    update ns = updateNs ns . fmap (updateRefs ns) . fmap (updateSynMatch ns)

    updateRefs ns = mapPT newref
      where
        newref (PRef fc fcs n) = PRef fc fcs (updateB ns n)
        newref t = t

    -- Below is a lot of tedious boilerplate which updates any top level
    -- names in the declaration. It will only change names which are bound in
    -- the declaration (including method names in interfaces and field names in
    -- record declarations, not including pattern variables)
    updateB :: [(Name, SynMatch)] -> Name -> Name
    updateB ns (NS n mods) = NS (updateB ns n) mods
    updateB ns n = case lookup n ns of
                        Just (SynBind tfc t) -> t
                        _ -> n

    updateNs :: [(Name, SynMatch)] -> PDecl -> PDecl
    updateNs ns (PTy doc argdoc s fc o n fc' t)
          = PTy doc argdoc s fc o (updateB ns n) fc' t
    updateNs ns (PClauses fc o n cs)
         = PClauses fc o (updateB ns n) (map (updateClause ns) cs)
    updateNs ns (PCAF fc n t) = PCAF fc (updateB ns n) t
    updateNs ns (PData ds cds s fc o dat)
         = PData ds cds s fc o (updateData ns dat)
    updateNs ns (PParams fc ps ds) = PParams fc ps (map (updateNs ns) ds)
    updateNs ns (PNamespace s fc ds) = PNamespace s fc (map (updateNs ns) ds)
    updateNs ns (PRecord doc syn fc o n fc' ps pdocs fields cname cdoc s)
         = PRecord doc syn fc o (updateB ns n) fc' ps pdocs
                   (map (updateField ns) fields)
                   (updateRecCon ns cname)
                   cdoc
                   s
    updateNs ns (PInterface docs s fc cs cn fc' ps pdocs pdets ds cname cdocs)
         = PInterface docs s fc cs (updateB ns cn) fc' ps pdocs pdets
                      (map (updateNs ns) ds)
                      (updateRecCon ns cname)
                      cdocs
    updateNs ns (PImplementation docs pdocs s fc cs pnames acc opts cn fc' ps pextra ity ni ds)
         = PImplementation docs pdocs s fc cs pnames acc opts (updateB ns cn) fc'
                           ps pextra ity (fmap (updateB ns) ni)
                           (map (updateNs ns) ds)
    updateNs ns (PMutual fc ds) = PMutual fc (map (updateNs ns) ds)
    updateNs ns (PProvider docs s fc fc' pw n)
        = PProvider docs s fc fc' pw (updateB ns n)
    updateNs ns d = d

    updateRecCon ns Nothing = Nothing
    updateRecCon ns (Just (n, fc)) = Just (updateB ns n, fc)

    updateField ns (m, p, t, doc) = (updateRecCon ns m, p, t, doc)

    updateClause ns (PClause fc n t ts t' ds)
       = PClause fc (updateB ns n) t ts t' (map (update ns) ds)
    updateClause ns (PWith fc n t ts t' m ds)
       = PWith fc (updateB ns n) t ts t' m (map (update ns) ds)
    updateClause ns (PClauseR fc ts t ds)
       = PClauseR fc ts t (map (update ns) ds)
    updateClause ns (PWithR fc ts t m ds)
       = PWithR fc ts t m (map (update ns) ds)

    updateData ns (PDatadecl n fc t cs)
       = PDatadecl (updateB ns n) fc t (map (updateCon ns) cs)
    updateData ns (PLaterdecl n fc t)
       = PLaterdecl (updateB ns n) fc t

    updateCon ns (cd, ads, cn, fc, ty, fc', fns)
       = (cd, ads, updateB ns cn, fc, ty, fc', fns)

    ruleGroup [] [] = True
    ruleGroup (s1:_) (s2:_) = s1 == s2
    ruleGroup _ _ = False

    extSymbol :: SSymbol -> IdrisParser (Maybe (Name, SynMatch))
    extSymbol (Keyword n) = do fc <- reservedFC (show n)
                               highlightP fc AnnKeyword
                               return Nothing
    extSymbol (Expr n) = do tm <- expr syn
                            return $ Just (n, SynTm tm)
    extSymbol (SimpleExpr n) = do tm <- simpleExpr syn
                                  return $ Just (n, SynTm tm)
    extSymbol (Binding n) = do (b, fc) <- name
                               return $ Just (n, SynBind fc b)
    extSymbol (Symbol s) = do fc <- symbolFC s
                              highlightP fc AnnKeyword
                              return Nothing

{-| Parses a syntax extension declaration (and adds the rule to parser state)

@
  SyntaxDecl ::= SyntaxRule;
@
-}
syntaxDecl :: SyntaxInfo -> IdrisParser PDecl
syntaxDecl syn = do s <- syntaxRule syn
                    i <- get
                    put (i `addSyntax` s)
                    fc <- getFC
                    return (PSyntax fc s)

-- | Extend an 'IState' with a new syntax extension. See also 'addReplSyntax'.
addSyntax :: IState -> Syntax -> IState
addSyntax i s = i { syntax_rules = updateSyntaxRules [s] rs,
                    syntax_keywords = ks ++ ns,
                    ibc_write = IBCSyntax s : map IBCKeyword ks ++ ibc }
  where rs = syntax_rules i
        ns = syntax_keywords i
        ibc = ibc_write i
        ks = map show (syntaxNames s)

-- | Like 'addSyntax', but no effect on the IBC.
addReplSyntax :: IState -> Syntax -> IState
addReplSyntax i s = i { syntax_rules = updateSyntaxRules [s] rs,
                        syntax_keywords = ks ++ ns }
  where rs = syntax_rules i
        ns = syntax_keywords i
        ks = map show (syntaxNames s)

{-| Parses a syntax extension declaration

@
SyntaxRuleOpts ::= 'term' | 'pattern';
@

@
SyntaxRule ::=
  SyntaxRuleOpts? 'syntax' SyntaxSym+ '=' TypeExpr Terminator;
@

@
SyntaxSym ::=   '[' Name_t ']'
             |  '{' Name_t '}'
             |  Name_t
             |  StringLiteral_t
             ;
@
-}
syntaxRule :: SyntaxInfo -> IdrisParser Syntax
syntaxRule syn
    = do sty <- try (do
            pushIndent
            sty <- option AnySyntax
                          (do reservedHL "term"; return TermSyntax
                           <|> do reservedHL "pattern"; return PatternSyntax)
            reservedHL "syntax"
            return sty)
         syms <- some syntaxSym
         when (all isExpr syms) $ unexpected "missing keywords in syntax rule"
         let ns = mapMaybe getName syms
         when (length ns /= length (nub ns))
            $ unexpected "repeated variable in syntax rule"
         lchar '='
         tm <- typeExpr (allowImp syn) >>= uniquifyBinders [n | Binding n <- syms]
         terminator
         return (Rule (mkSimple syms) tm sty)
  <|> do reservedHL "decl"; reservedHL "syntax"
         syms <- some syntaxSym
         when (all isExpr syms) $ unexpected "missing keywords in syntax rule"
         let ns = mapMaybe getName syms
         when (length ns /= length (nub ns))
            $ unexpected "repeated variable in syntax rule"
         lchar '='
         openBlock
         dec <- some (decl syn)
         closeBlock
         return (DeclRule (mkSimple syms) (concat dec))
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
    -- Can't parse a full expression followed by operator like characters due to ambiguity
    mkSimple' (Expr e : Symbol s : es)
      | takeWhile (`elem` opChars) ts /= "" = SimpleExpr e : Symbol s : mkSimple' es
       where ts = dropWhile isSpace . dropWhileEnd isSpace $ s
    mkSimple' (e : es) = e : mkSimple' es
    mkSimple' [] = []

    -- Prevent syntax variable capture by making all binders under syntax unique
    -- (the ol' Common Lisp GENSYM approach)
    uniquifyBinders :: [Name] -> PTerm -> IdrisParser PTerm
    uniquifyBinders userNames = fixBind 0 []
      where
        fixBind :: Int -> [(Name, Name)] -> PTerm -> IdrisParser PTerm
        fixBind 0 rens (PRef fc hls n) | Just n' <- lookup n rens =
          return $ PRef fc hls n'
        fixBind 0 rens (PPatvar fc n) | Just n' <- lookup n rens =
          return $ PPatvar fc n'
        fixBind 0 rens (PLam fc n nfc ty body)
          | n `elem` userNames = liftM2 (PLam fc n nfc)
                                        (fixBind 0 rens ty)
                                        (fixBind 0 rens body)
          | otherwise =
            do ty' <- fixBind 0 rens ty
               n' <- gensym n
               body' <- fixBind 0 ((n,n'):rens) body
               return $ PLam fc n' nfc ty' body'
        fixBind 0 rens (PPi plic n nfc argTy body)
          | n `elem` userNames = liftM2 (PPi plic n nfc)
                                        (fixBind 0 rens argTy)
                                        (fixBind 0 rens body)
          | otherwise =
            do ty' <- fixBind 0 rens argTy
               n' <- gensym n
               body' <- fixBind 0 ((n,n'):rens) body
               return $ (PPi plic n' nfc ty' body')
        fixBind 0 rens (PLet fc n nfc ty val body)
          | n `elem` userNames = liftM3 (PLet fc n nfc)
                                        (fixBind 0 rens ty)
                                        (fixBind 0 rens val)
                                        (fixBind 0 rens body)
          | otherwise =
            do ty' <- fixBind 0 rens ty
               val' <- fixBind 0 rens val
               n' <- gensym n
               body' <- fixBind 0 ((n,n'):rens) body
               return $ PLet fc n' nfc ty' val' body'
        fixBind 0 rens (PMatchApp fc n) | Just n' <- lookup n rens =
          return $ PMatchApp fc n'
        -- Also rename resolved quotations, to allow syntax rules to
        -- have quoted references to their own bindings.
        fixBind 0 rens (PQuoteName n True fc) | Just n' <- lookup n rens =
          return $ PQuoteName n' True fc

        -- Don't mess with quoted terms
        fixBind q rens (PQuasiquote tm goal) =
          flip PQuasiquote goal <$> fixBind (q + 1) rens tm
        fixBind q rens (PUnquote tm) =
          PUnquote <$> fixBind (q - 1) rens tm

        fixBind q rens x = descendM (fixBind q rens) x

        gensym :: Name -> IdrisParser Name
        gensym n = do ist <- get
                      let idx = idris_name ist
                      put ist { idris_name = idx + 1 }
                      return $ sMN idx (show n)

{-| Parses a syntax symbol (either binding variable, keyword or expression)

@
SyntaxSym ::=   '[' Name_t ']'
             |  '{' Name_t '}'
             |  Name_t
             |  StringLiteral_t
             ;
@
 -}
syntaxSym :: IdrisParser SSymbol
syntaxSym =    try (do lchar '['; n <- fst <$> name; lchar ']'
                       return (Expr n))
            <|> try (do lchar '{'; n <- fst <$> name; lchar '}'
                        return (Binding n))
            <|> do n <- fst <$> iName []
                   return (Keyword n)
            <|> do sym <- fmap fst stringLiteral
                   return (Symbol sym)
            <?> "syntax symbol"

{-| Parses a function declaration with possible syntax sugar

@
  FunDecl ::= FunDecl';
@
-}
fnDecl :: SyntaxInfo -> IdrisParser [PDecl]
fnDecl syn = try (do notEndBlock
                     d <- fnDecl' syn
                     i <- get
                     let d' = fmap (desugar syn i) d
                     return [d']) <?> "function declaration"

{-| Parses a function declaration

@
 FunDecl' ::=
  DocComment_t? FnOpts* Accessibility? FnOpts* FnName TypeSig Terminator
  | Postulate
  | Pattern
  | CAF
  ;
@
-}
fnDecl' :: SyntaxInfo -> IdrisParser PDecl
fnDecl' syn = checkDeclFixity $
              do (doc, argDocs, fc, opts', n, nfc, acc) <- try (do
                        pushIndent
                        (doc, argDocs) <- docstring syn
                        (opts, acc) <- fnOpts
                        (n_in, nfc) <- fnName
                        let n = expandNS syn n_in
                        fc <- getFC
                        lchar ':'
                        return (doc, argDocs, fc, opts, n, nfc, acc))
                 ty <- typeExpr (allowImp syn)
                 terminator
                 -- If it's a top level function, note the accessibility
                 -- rules
                 when (syn_toplevel syn) $ addAcc n acc
                 return (PTy doc argDocs syn fc opts' n nfc ty)
            <|> postulate syn
            <|> caf syn
            <|> pattern syn
            <?> "function declaration"

{-| Parses a series of function and accessbility options

@
FnOpts ::= FnOpt* Accessibility FnOpt*
@
 -}
fnOpts :: IdrisParser ([FnOpt], Accessibility)
fnOpts = do
    opts <- many fnOpt
    acc <- accessibility
    opts' <- many fnOpt
    let allOpts = opts ++ opts'
    let existingTotality = allOpts `intersect` [TotalFn, CoveringFn, PartialFn]
    opts'' <- addDefaultTotality (nub existingTotality) allOpts
    return (opts'', acc)
  where prettyTot TotalFn = "total"
        prettyTot PartialFn = "partial"
        prettyTot CoveringFn = "covering"
        addDefaultTotality [] opts = do
          ist <- get
          case default_total ist of
            DefaultCheckingTotal    -> return (TotalFn:opts)
            DefaultCheckingCovering -> return (CoveringFn:opts)
            DefaultCheckingPartial  -> return opts -- Don't add partial so that --warn-partial still reports warnings if necessary
        addDefaultTotality [tot] opts = return opts
        -- Should really be a semantics error instead of a parser error
        addDefaultTotality (tot1:tot2:tots) opts =
          fail ("Conflicting totality modifiers specified " ++ prettyTot tot1 ++ " and " ++ prettyTot tot2)


{-| Parses a function option

@
FnOpt ::= 'total'
  | 'partial'
  | 'covering'
  | 'implicit'
  | '%' 'no_implicit'
  | '%' 'assert_total'
  | '%' 'error_handler'
  | '%' 'reflection'
  | '%' 'specialise' '[' NameTimesList? ']'
  ;
@

@
NameTimes ::= FnName Natural?;
@

@
NameTimesList ::=
  NameTimes
  | NameTimes ',' NameTimesList
  ;
@
-}
fnOpt :: IdrisParser FnOpt
fnOpt = do reservedHL "total"; return TotalFn
        <|> do reservedHL "partial"; return PartialFn
        <|> do reservedHL "covering"; return CoveringFn
        <|> do try (lchar '%' *> reserved "export"); c <- fmap fst stringLiteral;
                    return $ CExport c
        <|> do try (lchar '%' *> reserved "no_implicit");
                    return NoImplicit
        <|> do try (lchar '%' *> reserved "inline");
                    return Inlinable
        <|> do try (lchar '%' *> reserved "static");
                    return StaticFn
        <|> do try (lchar '%' *> reserved "assert_total");
               fc <- getFC
               parserWarning fc Nothing (Msg "%assert_total is deprecated. Use the 'assert_total' function instead.")
               return AssertTotal
        <|> do try (lchar '%' *> reserved "error_handler");
                    return ErrorHandler
        <|> do try (lchar '%' *> reserved "error_reverse");
                    return ErrorReverse
        <|> do try (lchar '%' *> reserved "error_reduce");
                    return ErrorReduce
        <|> do try (lchar '%' *> reserved "reflection");
                    return Reflection
        <|> do try (lchar '%' *> reserved "hint");
                    return AutoHint
        <|> do try (lchar '%' *> reserved "overlapping");
                    return OverlappingDictionary
        <|> do lchar '%'; reserved "specialise";
               lchar '['; ns <- sepBy nameTimes (lchar ','); lchar ']';
               return $ Specialise ns
        <|> do reservedHL "implicit"; return Implicit
        <?> "function modifier"
  where nameTimes :: IdrisParser (Name, Maybe Int)
        nameTimes = do n <- fst <$> fnName
                       t <- option Nothing (do reds <- fmap fst natural
                                               return (Just (fromInteger reds)))
                       return (n, t)

{-| Parses a postulate

@
Postulate ::=
  DocComment_t? 'postulate' FnOpts* Accesibility? FnOpts* FnName TypeSig Terminator
  ;
@
-}
postulate :: SyntaxInfo -> IdrisParser PDecl
postulate syn = do (doc, ext)
                       <- try $ do (doc, _) <- docstring syn
                                   pushIndent
                                   ext <- ppostDecl
                                   return (doc, ext)
                   ist <- get
                   (opts, acc) <- fnOpts
                   (n_in, nfc) <- fnName
                   let n = expandNS syn n_in
                   lchar ':'
                   ty <- typeExpr (allowImp syn)
                   fc <- getFC
                   terminator
                   addAcc n acc
                   return (PPostulate ext doc syn fc nfc opts n ty)
                 <?> "postulate"
   where ppostDecl = do fc <- reservedHL "postulate"; return False
                 <|> do lchar '%'; reserved "extern"; return True

{-| Parses a using declaration

@
Using ::=
  'using' '(' UsingDeclList ')' OpenBlock Decl* CloseBlock
  ;
@
 -}
using_ :: SyntaxInfo -> IdrisParser [PDecl]
using_ syn =
    do reservedHL "using"
       lchar '('; ns <- usingDeclList syn; lchar ')'
       openBlock
       let uvars = using syn
       ds <- many (decl (syn { using = uvars ++ ns }))
       closeBlock
       return (concat ds)
    <?> "using declaration"

{-| Parses a parameters declaration

@
Params ::=
  'parameters' '(' TypeDeclList ')' OpenBlock Decl* CloseBlock
  ;
@
-}
params :: SyntaxInfo -> IdrisParser [PDecl]
params syn =
    do reservedHL "parameters"; lchar '('; ns <- typeDeclList syn; lchar ')'
       let ns' = [(n, ty) | (_, n, _, ty) <- ns]
       openBlock
       let pvars = syn_params syn
       ds <- many (decl syn { syn_params = pvars ++ ns' })
       closeBlock
       fc <- getFC
       return [PParams fc ns' (concat ds)]
    <?> "parameters declaration"

-- | Parses an open block
openInterface :: SyntaxInfo -> IdrisParser [PDecl]
openInterface syn =
    do reservedHL "using"
       reservedHL "implementation"
       fc <- getFC
       ns <- sepBy1 fnName (lchar ',')

       openBlock
       ds <- many (decl syn)
       closeBlock
       return [POpenInterfaces fc (map fst ns) (concat ds)]
    <?> "open interface declaration"





{-| Parses a mutual declaration (for mutually recursive functions)

@
Mutual ::=
  'mutual' OpenBlock Decl* CloseBlock
  ;
@
-}
mutual :: SyntaxInfo -> IdrisParser [PDecl]
mutual syn =
    do reservedHL "mutual"
       openBlock
       let pvars = syn_params syn
       ds <- many (decl (syn { mut_nesting = mut_nesting syn + 1 } ))
       closeBlock
       fc <- getFC
       return [PMutual fc (concat ds)]
    <?> "mutual block"

{-| Parses a namespace declaration

@
Namespace ::=
  'namespace' identifier OpenBlock Decl+ CloseBlock
  ;
@
-}
namespace :: SyntaxInfo -> IdrisParser [PDecl]
namespace syn =
    do reservedHL "namespace"
       (n, nfc) <- identifier
       openBlock
       ds <- some (decl syn { syn_namespace = n : syn_namespace syn })
       closeBlock
       return [PNamespace n nfc (concat ds)]
     <?> "namespace declaration"

{-| Parses a methods block (for implementations)

@
  ImplementationBlock ::= 'where' OpenBlock FnDecl* CloseBlock
@
-}
implementationBlock :: SyntaxInfo -> IdrisParser [PDecl]
implementationBlock syn = do reservedHL "where"
                             openBlock
                             ds <- many (fnDecl syn)
                             closeBlock
                             return (concat ds)
                          <?> "implementation block"

{-| Parses a methods and implementations block (for interfaces)

@
MethodOrImplementation ::=
   FnDecl
   | Implementation
   ;
@

@
InterfaceBlock ::=
  'where' OpenBlock Constructor? MethodOrImplementation* CloseBlock
  ;
@
-}
interfaceBlock :: SyntaxInfo -> IdrisParser (Maybe (Name, FC), Docstring (Either Err PTerm), [PDecl])
interfaceBlock syn = do reservedHL "where"
                        openBlock
                        (cn, cd) <- option (Nothing, emptyDocstring) $
                                    try (do (doc, _) <- option noDocs docComment
                                            n <- constructor
                                            return (Just n, doc))
                        ist <- get
                        let cd' = annotate syn ist cd

                        ds <- many (notEndBlock >> try (implementation True syn)
                                                   <|> do x <- data_ syn
                                                          return [x]
                                                   <|> fnDecl syn)
                        closeBlock
                        return (cn, cd', concat ds)
                     <?> "interface block"
  where
    constructor :: IdrisParser (Name, FC)
    constructor = reservedHL "constructor" *> fnName

    annotate :: SyntaxInfo -> IState -> Docstring () -> Docstring (Either Err PTerm)
    annotate syn ist = annotCode $ tryFullExpr syn ist

{-| Parses an interface declaration

@
InterfaceArgument ::=
   Name
   | '(' Name ':' Expr ')'
   ;
@

@
Interface ::=
  DocComment_t? Accessibility? 'interface' ConstraintList? Name InterfaceArgument* InterfaceBlock?
  ;
@
-}
interface_ :: SyntaxInfo -> IdrisParser [PDecl]
interface_ syn = do (doc, argDocs, acc)
                      <- try (do (doc, argDocs) <- docstring syn
                                 acc <- accessibility
                                 interfaceKeyword
                                 return (doc, argDocs, acc))
                    fc <- getFC
                    cons <- constraintList syn
                    let cons' = [(c, ty) | (_, c, _, ty) <- cons]
                    (n_in, nfc) <- fnName
                    let n = expandNS syn n_in
                    cs <- many carg
                    fds <- option [(cn, NoFC) | (cn, _, _) <- cs] fundeps
                    (cn, cd, ds) <- option (Nothing, fst noDocs, []) (interfaceBlock syn)
                    accData acc n (concatMap declared ds)
                    return [PInterface doc syn fc cons' n nfc cs argDocs fds ds cn cd]
                 <?> "interface declaration"
  where
    fundeps :: IdrisParser [(Name, FC)]
    fundeps = do lchar '|'; sepBy name (lchar ',')

    interfaceKeyword :: IdrisParser ()
    interfaceKeyword = reservedHL "interface"
               <|> do reservedHL "class"
                      fc <- getFC
                      parserWarning fc Nothing (Msg "The 'class' keyword is deprecated. Use 'interface' instead.")

    carg :: IdrisParser (Name, FC, PTerm)
    carg = do lchar '('; (i, ifc) <- name; lchar ':'; ty <- expr syn; lchar ')'
              return (i, ifc, ty)
       <|> do (i, ifc) <- name
              fc <- getFC
              return (i, ifc, PType fc)

{-| Parses an interface implementation declaration

@
  Implementation ::=
    DocComment_t? 'implementation' ImplementationName? ConstraintList? Name SimpleExpr* ImplementationBlock?
    ;
@

@
ImplementationName ::= '[' Name ']';
@
-}
implementation :: Bool -> SyntaxInfo -> IdrisParser [PDecl]
implementation kwopt syn
                   = do ist <- get
                        (doc, argDocs) <- docstring syn
                        (opts, acc) <- fnOpts
                        if kwopt then optional implementationKeyword
                                 else do implementationKeyword
                                         return (Just ())

                        fc <- getFC
                        en <- optional implementationName
                        cs <- constraintList syn
                        let cs' = [(c, ty) | (_, c, _, ty) <- cs]
                        (cn, cnfc) <- fnName
                        args <- many (simpleExpr syn)
                        let sc = PApp fc (PRef cnfc [cnfc] cn) (map pexp args)
                        let t = bindList (\r -> PPi constraint { pcount = r }) cs sc
                        pnames <- implementationUsing
                        ds <- implementationBlock syn
                        return [PImplementation doc argDocs syn fc cs' pnames acc opts cn cnfc args [] t en ds]
                      <?> "implementation declaration"
  where implementationName :: IdrisParser Name
        implementationName = do lchar '['; n_in <- fst <$> fnName; lchar ']'
                                let n = expandNS syn n_in
                                return n
                             <?> "implementation name"
        implementationKeyword :: IdrisParser ()
        implementationKeyword = reservedHL "implementation"
                         <|> do reservedHL "instance"
                                fc <- getFC
                                parserWarning fc Nothing (Msg "The 'instance' keyword is deprecated. Use 'implementation' (or omit it) instead.")

        implementationUsing :: IdrisParser [Name]
        implementationUsing = do reservedHL "using"
                                 ns <- sepBy1 fnName (lchar ',')
                                 return (map fst ns)
                              <|> return []

-- | Parse a docstring
docstring :: SyntaxInfo
          -> IdrisParser (Docstring (Either Err PTerm),
                          [(Name,Docstring (Either Err PTerm))])
docstring syn = do (doc, argDocs) <- option noDocs docComment
                   ist <- get
                   let doc' = annotCode (tryFullExpr syn ist) doc
                       argDocs' = [ (n, annotCode (tryFullExpr syn ist) d)
                                  | (n, d) <- argDocs ]
                   return (doc', argDocs')


{-| Parses a using declaration list

@
UsingDeclList ::=
  UsingDeclList'
  | NameList TypeSig
  ;
@

@
UsingDeclList' ::=
  UsingDecl
  | UsingDecl ',' UsingDeclList'
  ;
@

@
NameList ::=
  Name
  | Name ',' NameList
  ;
@
-}
usingDeclList :: SyntaxInfo -> IdrisParser [Using]
usingDeclList syn
               = try (sepBy1 (usingDecl syn) (lchar ','))
             <|> do ns <- sepBy1 (fst <$> name) (lchar ',')
                    lchar ':'
                    t <- typeExpr (disallowImp syn)
                    return (map (\x -> UImplicit x t) ns)
             <?> "using declaration list"

{-| Parses a using declaration

@
UsingDecl ::=
  FnName TypeSig
  | FnName FnName+
  ;
@
-}
usingDecl :: SyntaxInfo -> IdrisParser Using
usingDecl syn = try (do x <- fst <$> fnName
                        lchar ':'
                        t <- typeExpr (disallowImp syn)
                        return (UImplicit x t))
            <|> do c <- fst <$> fnName
                   xs <- many (fst <$> fnName)
                   return (UConstraint c xs)
            <?> "using declaration"

{-| Parse a clause with patterns

@
Pattern ::= Clause;
@
-}
pattern :: SyntaxInfo -> IdrisParser PDecl
pattern syn = do fc <- getFC
                 clause <- clause syn
                 return (PClauses fc [] (sMN 2 "_") [clause]) -- collect together later
              <?> "pattern"

{-| Parse a constant applicative form declaration

@
CAF ::= 'let' FnName '=' Expr Terminator;
@
-}
caf :: SyntaxInfo -> IdrisParser PDecl
caf syn = do reservedHL "let"
             n_in <- fst <$> fnName; let n = expandNS syn n_in
             pushIndent
             lchar '='
             t <- indented $ expr syn
             terminator
             fc <- getFC
             return (PCAF fc n t)
           <?> "constant applicative form declaration"

{-| Parse an argument expression

@
ArgExpr ::= HSimpleExpr | {- In Pattern External (User-defined) Expression -};
@
-}
argExpr :: SyntaxInfo -> IdrisParser PTerm
argExpr syn = let syn' = syn { inPattern = True } in
                  try (hsimpleExpr syn') <|> simpleExternalExpr syn'
              <?> "argument expression"

{-| Parse a right hand side of a function

@
RHS ::= '='            Expr
     |  '?='  RHSName? Expr
     |  Impossible
     ;
@

@
RHSName ::= '{' FnName '}';
@
-}
rhs :: SyntaxInfo -> Name -> IdrisParser PTerm
rhs syn n = do lchar '='
               indentPropHolds gtProp
               expr syn
        <|> do symbol "?=";
               fc <- getFC
               name <- option n' (do symbol "{"; n <- fst <$> fnName; symbol "}";
                                     return n)
               r <- expr syn
               return (addLet fc name r)
        <|> impossible
        <?> "function right hand side"
  where mkN :: Name -> Name
        mkN (UN x)   = if (tnull x || not (isAlpha (thead x)))
                         then sUN "infix_op_lemma_1"
                         else sUN (str x++"_lemma_1")
        mkN (NS x n) = NS (mkN x) n
        n' :: Name
        n' = mkN n
        addLet :: FC -> Name -> PTerm -> PTerm
        addLet fc nm (PLet fc' n nfc ty val r) = PLet fc' n nfc ty val (addLet fc nm r)
        addLet fc nm (PCase fc' t cs) = PCase fc' t (map addLetC cs)
          where addLetC (l, r) = (l, addLet fc nm r)
        addLet fc nm r = (PLet fc (sUN "value") NoFC Placeholder r (PMetavar NoFC nm))

{-|Parses a function clause

@
RHSOrWithBlock ::= RHS WhereOrTerminator
               | 'with' SimpleExpr OpenBlock FnDecl+ CloseBlock
               ;
@

@
Clause ::=                                                               WExpr+ RHSOrWithBlock
       |   SimpleExpr '<=='  FnName                                             RHS WhereOrTerminator
       |   ArgExpr Operator ArgExpr                                      WExpr* RHSOrWithBlock {- Except "=" and "?=" operators to avoid ambiguity -}
       |                     FnName ConstraintArg* ImplicitOrArgExpr*    WExpr* RHSOrWithBlock
       ;
@

@
ImplicitOrArgExpr ::= ImplicitArg | ArgExpr;
@

@
WhereOrTerminator ::= WhereBlock | Terminator;
@
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
                  let wsyn = syn { syn_namespace = [], syn_toplevel = False }
                  (wheres, nmap) <- choice [do x <- whereBlock n wsyn
                                               popIndent
                                               return x,
                                            do terminator
                                               return ([], [])]
                  return $ PClauseR fc wargs r wheres) <|> (do
                  popIndent
                  reservedHL "with"
                  wval <- simpleExpr syn
                  pn <- optProof
                  openBlock
                  ds <- some $ fnDecl syn
                  let withs = concat ds
                  closeBlock
                  return $ PWithR fc wargs wval pn withs)
       <|> do ty <- try (do pushIndent
                            ty <- simpleExpr syn
                            symbol "<=="
                            return ty)
              fc <- getFC
              n_in <- fst <$> fnName; let n = expandNS syn n_in
              r <- rhs syn n
              ist <- get
              let ctxt = tt_ctxt ist
              let wsyn = syn { syn_namespace = [] }
              (wheres, nmap) <- choice [do x <- whereBlock n wsyn
                                           popIndent
                                           return x,
                                        do terminator
                                           return ([], [])]
              let capp = PLet fc (sMN 0 "match") NoFC
                              ty
                              (PMatchApp fc n)
                              (PRef fc [] (sMN 0 "match"))
              ist <- get
              put (ist { lastParse = Just n })
              return $ PClause fc n capp [] r wheres
       <|> do (l, op, nfc) <- try (do
                pushIndent
                l <- argExpr syn
                (op, nfc) <- operatorFC
                when (op == "=" || op == "?=" ) $
                     fail "infix clause definition with \"=\" and \"?=\" not supported "
                return (l, op, nfc))
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
                  let capp = PApp fc (PRef nfc [nfc] n) [pexp l, pexp r]
                  put (ist { lastParse = Just n })
                  return $ PClause fc n capp wargs rs wheres) <|> (do
                   popIndent
                   reservedHL "with"
                   wval <- bracketed syn
                   pn <- optProof
                   openBlock
                   ds <- some $ fnDecl syn
                   closeBlock
                   ist <- get
                   let capp = PApp fc (PRef fc [] n) [pexp l, pexp r]
                   let withs = map (fillLHSD n capp wargs) $ concat ds
                   put (ist { lastParse = Just n })
                   return $ PWith fc n capp wargs wval pn withs)
       <|> do pushIndent
              (n_in, nfc) <- fnName; let n = expandNS syn n_in
              fc <- getFC
              args <- many (try (implicitArg (syn { inPattern = True } ))
                            <|> try (constraintArg (syn { inPattern = True }))
                            <|> (fmap pexp (argExpr syn)))
              wargs <- many (wExpr syn)
              let capp = PApp fc (PRef nfc [nfc] n) args
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
                   reservedHL "with"
                   ist <- get
                   put (ist { lastParse = Just n })
                   wval <- bracketed syn
                   pn <- optProof
                   openBlock
                   ds <- some $ fnDecl syn
                   let withs = map (fillLHSD n capp wargs) $ concat ds
                   closeBlock
                   popIndent
                   return $ PWith fc n capp wargs wval pn withs)
      <?> "function clause"
  where
    optProof = option Nothing (do reservedHL "proof"
                                  n <- fnName
                                  return (Just n))

    fillLHS :: Name -> PTerm -> [PTerm] -> PClause -> PClause
    fillLHS n capp owargs (PClauseR fc wargs v ws)
       = PClause fc n capp (owargs ++ wargs) v ws
    fillLHS n capp owargs (PWithR fc wargs v pn ws)
       = PWith fc n capp (owargs ++ wargs) v pn
            (map (fillLHSD n capp (owargs ++ wargs)) ws)
    fillLHS _ _ _ c = c

    fillLHSD :: Name -> PTerm -> [PTerm] -> PDecl -> PDecl
    fillLHSD n c a (PClauses fc o fn cs) = PClauses fc o fn (map (fillLHS n c a) cs)
    fillLHSD n c a x = x

{-| Parses with pattern

@
WExpr ::= '|' Expr';
@
-}
wExpr :: SyntaxInfo -> IdrisParser PTerm
wExpr syn = do lchar '|'
               expr' (syn { inPattern = True })
            <?> "with pattern"

{-| Parses a where block

@
WhereBlock ::= 'where' OpenBlock Decl+ CloseBlock;
@
-}
whereBlock :: Name -> SyntaxInfo -> IdrisParser ([PDecl], [(Name, Name)])
whereBlock n syn
    = do reservedHL "where"
         ds <- indentedBlock1 (decl syn)
         let dns = concatMap (concatMap declared) ds
         return (concat ds, map (\x -> (x, decoration syn x)) dns)
      <?> "where block"

{-|Parses a code generation target language name

@
Codegen ::= 'C'
        |   'Java'
        |   'JavaScript'
        |   'Node'
        |   'LLVM'
        |   'Bytecode'
        ;
@
-}
codegen_ :: IdrisParser Codegen
codegen_ = do n <- fst <$> identifier
              return (Via IBCFormat (map toLower n))
       <|> do reserved "Bytecode"; return Bytecode
       <?> "code generation language"

{-|Parses a compiler directive
@
StringList ::=
  String
  | String ',' StringList
  ;
@

@
Directive ::= '%' Directive';
@

@
Directive' ::= 'lib'            CodeGen String_t
           |   'link'           CodeGen String_t
           |   'flag'           CodeGen String_t
           |   'include'        CodeGen String_t
           |   'hide'           Name
           |   'freeze'         Name
           |   'thaw'           Name
           |   'access'         Accessibility
           |   'default'        Totality
           |   'logging'        Natural
           |   'dynamic'        StringList
           |   'name'           Name NameList
           |   'error_handlers' Name NameList
           |   'language'       'TypeProviders'
           |   'language'       'ErrorReflection'
           |   'deprecated' Name String
           |   'fragile'    Name Reason
           ;
@
-}
directive :: SyntaxInfo -> IdrisParser [PDecl]
directive syn = do try (lchar '%' *> reserved "lib")
                   cgn <- codegen_
                   lib <- fmap fst stringLiteral
                   return [PDirective (DLib cgn lib)]
             <|> do try (lchar '%' *> reserved "link")
                    cgn <- codegen_; obj <- fst <$> stringLiteral
                    return [PDirective (DLink cgn obj)]
             <|> do try (lchar '%' *> reserved "flag")
                    cgn <- codegen_; flag <- fst <$> stringLiteral
                    return [PDirective (DFlag cgn flag)]
             <|> do try (lchar '%' *> reserved "include")
                    cgn <- codegen_
                    hdr <- fst <$> stringLiteral
                    return [PDirective (DInclude cgn hdr)]
             <|> do try (lchar '%' *> reserved "hide"); n <- fst <$> fnName
                    return [PDirective (DHide n)]
             <|> do try (lchar '%' *> reserved "freeze"); n <- fst <$> iName []
                    return [PDirective (DFreeze n)]
             <|> do try (lchar '%' *> reserved "thaw"); n <- fst <$> iName []
                    return [PDirective (DThaw n)]
             -- injectivity assertins are intended for debugging purposes
             -- only, and won't be documented/could be removed at any point
             <|> do try (lchar '%' *> reserved "assert_injective"); n <- fst <$> fnName
                    return [PDirective (DInjective n)]
             -- Assert totality of something after definition. This is
             -- here as a debugging aid, so commented out...
--              <|> do try (lchar '%' *> reserved "assert_set_total"); n <- fst <$> fnName
--                     return [PDirective (DSetTotal n)]
             <|> do try (lchar '%' *> reserved "access")
                    acc <- accessibility
                    ist <- get
                    put ist { default_access = acc }
                    return [PDirective (DAccess acc)]
             <|> do try (lchar '%' *> reserved "default"); tot <- totality
                    i <- get
                    put (i { default_total = tot } )
                    return [PDirective (DDefault tot)]
             <|> do try (lchar '%' *> reserved "logging")
                    i <- fst <$> natural
                    return [PDirective (DLogging i)]
             <|> do try (lchar '%' *> reserved "dynamic")
                    libs <- sepBy1 (fmap fst stringLiteral) (lchar ',')
                    return [PDirective (DDynamicLibs libs)]
             <|> do try (lchar '%' *> reserved "name")
                    (ty, tyFC) <- fnName
                    ns <- sepBy1 name (lchar ',')
                    return [PDirective (DNameHint ty tyFC ns)]
             <|> do try (lchar '%' *> reserved "error_handlers")
                    (fn, nfc) <- fnName
                    (arg, afc) <- fnName
                    ns <- sepBy1 name (lchar ',')
                    return [PDirective (DErrorHandlers fn nfc arg afc ns) ]
             <|> do try (lchar '%' *> reserved "language"); ext <- pLangExt;
                    return [PDirective (DLanguage ext)]
             <|> do try (lchar '%' *> reserved "deprecate")
                    n <- fst <$> fnName
                    alt <- option "" (fst <$> stringLiteral)
                    return [PDirective (DDeprecate n alt)]
             <|> do try (lchar '%' *> reserved "fragile")
                    n <- fst <$> fnName
                    alt <- option "" (fst <$> stringLiteral)
                    return [PDirective (DFragile n alt)]
             <|> do fc <- getFC
                    try (lchar '%' *> reserved "used")
                    fn <- fst <$> fnName
                    arg <- fst <$> iName []
                    return [PDirective (DUsed fc fn arg)]
             <|> do try (lchar '%' *> reserved "auto_implicits")
                    b <- on_off
                    return [PDirective (DAutoImplicits b)]
             <?> "directive"
  where on_off = do reserved "on"; return True
             <|> do reserved "off"; return False

pLangExt :: IdrisParser LanguageExt
pLangExt = (reserved "TypeProviders" >> return TypeProviders)
       <|> (reserved "ErrorReflection" >> return ErrorReflection)
       <|> (reserved "UniquenessTypes" >> return UniquenessTypes)
       <|> (reserved "LinearTypes" >> return LinearTypes)
       <|> (reserved "DSLNotation" >> return DSLNotation)
       <|> (reserved "ElabReflection" >> return ElabReflection)
       <|> (reserved "FirstClassReflection" >> return FCReflection)

{-| Parses a totality

@
Totality ::= 'partial' | 'total' | 'covering'
@

-}
totality :: IdrisParser DefaultTotality
totality
        = do reservedHL "total";   return DefaultCheckingTotal
      <|> do reservedHL "partial"; return DefaultCheckingPartial
      <|> do reservedHL "covering"; return DefaultCheckingCovering

{-| Parses a type provider

@
Provider ::= DocComment_t? '%' 'provide' Provider_What? '(' FnName TypeSig ')' 'with' Expr;
ProviderWhat ::= 'proof' | 'term' | 'type' | 'postulate'
@
 -}
provider :: SyntaxInfo -> IdrisParser [PDecl]
provider syn = do doc <- try (do (doc, _) <- docstring syn
                                 fc1 <- getFC
                                 lchar '%'
                                 fc2 <- reservedFC "provide"
                                 highlightP (spanFC fc1 fc2) AnnKeyword
                                 return doc)
                  provideTerm doc <|> providePostulate doc
               <?> "type provider"
  where provideTerm doc =
          do lchar '('; (n, nfc) <- fnName; lchar ':'; t <- typeExpr syn; lchar ')'
             fc <- getFC
             reservedHL "with"
             e <- expr syn <?> "provider expression"
             return  [PProvider doc syn fc nfc (ProvTerm t e) n]
        providePostulate doc =
          do reservedHL "postulate"
             (n, nfc) <- fnName
             fc <- getFC
             reservedHL "with"
             e <- expr syn <?> "provider expression"
             return [PProvider doc syn fc nfc (ProvPostulate e) n]

{-| Parses a transform

@
Transform ::= '%' 'transform' Expr '==>' Expr
@
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

{-| Parses a top-level reflected elaborator script

@
RunElabDecl ::= '%' 'runElab' Expr
@
-}
runElabDecl :: SyntaxInfo -> IdrisParser PDecl
runElabDecl syn =
  do kwFC <- try (do fc <- getFC
                     lchar '%'
                     fc' <- reservedFC "runElab"
                     return (spanFC fc fc'))
     script <- expr syn <?> "elaborator script"
     highlightP kwFC AnnKeyword
     return $ PRunElabDecl kwFC script (syn_namespace syn)
  <?> "top-level elaborator script"

{- * Loading and parsing -}
{-| Parses an expression from input -}
parseExpr :: IState -> String -> Result PTerm
parseExpr st = runparser (fullExpr defaultSyntax) st "(input)"

{-| Parses a constant form input -}
parseConst :: IState -> String -> Result Const
parseConst st = runparser (fmap fst constant) st "(input)"

{-| Parses a tactic from input -}
parseTactic :: IState -> String -> Result PTactic
parseTactic st = runparser (fullTactic defaultSyntax) st "(input)"

{-| Parses a do-step from input (used in the elab shell) -}
parseElabShellStep :: IState -> String -> Result (Either ElabShellCmd PDo)
parseElabShellStep ist = runparser (fmap Right (do_ defaultSyntax) <|> fmap Left elabShellCmd) ist "(input)"
  where elabShellCmd = char ':' >>
                       (reserved "qed"     >> pure EQED       ) <|>
                       (reserved "abandon" >> pure EAbandon   ) <|>
                       (reserved "undo"    >> pure EUndo      ) <|>
                       (reserved "state"   >> pure EProofState) <|>
                       (reserved "term"    >> pure EProofTerm ) <|>
                       (expressionTactic ["e", "eval"] EEval ) <|>
                       (expressionTactic ["t", "type"] ECheck) <|>
                       (expressionTactic ["search"] ESearch   ) <|>
                       (do reserved "doc"
                           doc <- (Right . fst <$> constant) <|> (Left . fst <$> fnName)
                           eof
                           return (EDocStr doc))
                       <?> "elab command"
        expressionTactic cmds tactic =
           do asum (map reserved cmds)
              t <- spaced (expr defaultSyntax)
              i <- get
              return $ tactic (desugar defaultSyntax i t)
        spaced parser = indentPropHolds gtProp *> parser

-- | Parse module header and imports
parseImports :: FilePath -> String -> Idris (Maybe (Docstring ()), [String], [ImportInfo], Maybe Delta)
parseImports fname input
    = do i <- getIState
         case parseString (runInnerParser (evalStateT imports i)) (Directed (UTF8.fromString fname) 0 0 0 0) input of
              Failure (ErrInfo err _) -> fail (show err)
              Success (x, annots, i) ->
                do putIState i
                   fname' <- runIO $ Dir.makeAbsolute fname
                   sendHighlighting $ addPath annots fname'
                   return x
  where imports :: IdrisParser ((Maybe (Docstring ()), [String],
                                 [ImportInfo],
                                 Maybe Delta),
                                [(FC, OutputAnnotation)], IState)
        imports = do whiteSpace
                     (mdoc, mname, annots) <- moduleHeader
                     ps_exp        <- many import_
                     mrk           <- mark
                     isEof         <- lookAheadMatches eof
                     let mrk' = if isEof
                                   then Nothing
                                   else Just mrk
                     i     <- get
                     -- add Builtins and Prelude, unless options say
                     -- not to
                     let ps = ps_exp -- imp "Builtins" : imp "Prelude" : ps_exp
                     return ((mdoc, mname, ps, mrk'), annots, i)

        imp m = ImportInfo False (toPath m)
                           Nothing [] NoFC NoFC
        ns = Spl.splitOn "."
        toPath = foldl1' (</>) . ns

        addPath :: [(FC, OutputAnnotation)] -> FilePath -> [(FC, OutputAnnotation)]
        addPath [] _ = []
        addPath ((fc, AnnNamespace ns Nothing) : annots) path =
           (fc, AnnNamespace ns (Just path)) : addPath annots path
        addPath (annot:annots) path = annot : addPath annots path

-- | There should be a better way of doing this...
findFC :: Doc -> (FC, String)
findFC x = let s = show (plain x) in findFC' s
  where findFC' s = case span (/= ':') s of
                      -- Horrid kludge to prevent crashes on Windows
                      (prefix, ':':'\\':rest) ->
                        case findFC' rest of
                          (NoFC, msg) -> (NoFC, msg)
                          (FileFC f, msg) -> (FileFC (prefix ++ ":\\" ++ f), msg)
                          (FC f start end, msg) -> (FC (prefix ++ ":\\" ++ f) start end, msg)
                      (failname, ':':rest) -> case span isDigit rest of
                        (line, ':':rest') -> case span isDigit rest' of
                          (col, ':':msg) -> let pos = (read line, read col) in
                                                (FC failname pos pos, msg)

-- | Check if the coloring matches the options and corrects if necessary
fixColour :: Bool -> ANSI.Doc -> ANSI.Doc
fixColour False doc = ANSI.plain doc
fixColour True doc  = doc

-- | A program is a list of declarations, possibly with associated
-- documentation strings.
parseProg :: SyntaxInfo -> FilePath -> String -> Maybe Delta ->
             Idris [PDecl]
parseProg syn fname input mrk
    = do i <- getIState
         case runparser mainProg i fname input of
            Failure (ErrInfo doc _)     -> do -- FIXME: Get error location from trifecta
                                  -- this can't be the solution!
                                  -- Issue #1575 on the issue tracker.
                                  --    https://github.com/idris-lang/Idris-dev/issues/1575
                                  let (fc, msg) = findFC doc
                                  i <- getIState
                                  case idris_outputmode i of
                                    RawOutput h  -> iputStrLn (show $ fixColour (idris_colourRepl i) doc)
                                    IdeMode n h -> iWarn fc (P.text msg)
                                  putIState (i { errSpan = Just fc })
                                  return []
            Success (x, i)  -> do putIState i
                                  reportParserWarnings
                                  return $ collect x
  where mainProg :: IdrisParser ([PDecl], IState)
        mainProg = case mrk of
                        Nothing -> do i <- get; return ([], i)
                        Just mrk -> do
                          release mrk
                          ds <- prog syn
                          i' <- get
                          return (ds, i')

{-| Load idris module and show error if something wrong happens -}
loadModule :: FilePath -> IBCPhase -> Idris (Maybe String)
loadModule f phase
   = idrisCatch (loadModule' f phase)
                (\e -> do setErrSpan (getErrSpan e)
                          ist <- getIState
                          iWarn (getErrSpan e) $ pprintErr ist e
                          return Nothing)

{-| Load idris module -}
loadModule' :: FilePath -> IBCPhase -> Idris (Maybe String)
loadModule' f phase
   = do i <- getIState
        let file = takeWhile (/= ' ') f
        ibcsd <- valIBCSubDir i
        ids <- allImportDirs
        fp <- findImport ids ibcsd file
        if file `elem` imported i
          then do logParser 1 $ "Already read " ++ file
                  return Nothing
          else do putIState (i { imported = file : imported i })
                  case fp of
                    IDR fn  -> loadSource False fn Nothing
                    LIDR fn -> loadSource True  fn Nothing
                    IBC fn src ->
                      idrisCatch (loadIBC True phase fn)
                                 (\c -> do logParser 1 $ fn ++ " failed " ++ pshow i c
                                           case src of
                                             IDR sfn -> loadSource False sfn Nothing
                                             LIDR sfn -> loadSource True sfn Nothing)
                  return $ Just file

{-| Load idris code from file -}
loadFromIFile :: Bool -> IBCPhase -> IFileType -> Maybe Int -> Idris ()
loadFromIFile reexp phase i@(IBC fn src) maxline
   = do logParser 1 $ "Skipping " ++ getSrcFile i
        idrisCatch (loadIBC reexp phase fn)
                (\err -> ierror $ LoadingFailed fn err)
  where
    getSrcFile (IDR fn) = fn
    getSrcFile (LIDR fn) = fn
    getSrcFile (IBC f src) = getSrcFile src

loadFromIFile _ _ (IDR fn) maxline = loadSource' False fn maxline
loadFromIFile _ _ (LIDR fn) maxline = loadSource' True fn maxline

{-| Load idris source code and show error if something wrong happens -}
loadSource' :: Bool -> FilePath -> Maybe Int -> Idris ()
loadSource' lidr r maxline
   = idrisCatch (loadSource lidr r maxline)
                (\e -> do setErrSpan (getErrSpan e)
                          ist <- getIState
                          case e of
                            At f e' -> iWarn f (pprintErr ist e')
                            _ -> iWarn (getErrSpan e) (pprintErr ist e))

{-| Load Idris source code-}
loadSource :: Bool -> FilePath -> Maybe Int -> Idris ()
loadSource lidr f toline
             = do logParser 1 ("Reading " ++ f)
                  iReport   2 ("Reading " ++ f)
                  i <- getIState
                  let def_total = default_total i
                  file_in <- runIO $ readSource f
                  file <- if lidr then tclift $ unlit f file_in else return file_in
                  (mdocs, mname, imports_in, pos) <- parseImports f file
                  ai <- getAutoImports
                  let imports = map (\n -> ImportInfo True n Nothing [] NoFC NoFC) ai ++ imports_in
                  ids <- allImportDirs
                  ibcsd <- valIBCSubDir i
                  mapM_ (\(re, f, ns, nfc) ->
                               do fp <- findImport ids ibcsd f
                                  case fp of
                                      LIDR fn -> ifail $ "No ibc for " ++ f
                                      IDR fn -> ifail $ "No ibc for " ++ f
                                      IBC fn src ->
                                        do loadIBC True IBC_Building fn
                                           let srcFn = case src of
                                                         IDR fn -> Just fn
                                                         LIDR fn -> Just fn
                                                         _ -> Nothing
                                           srcFnAbs <- case srcFn of
                                                         Just fn -> fmap Just (runIO $ Dir.makeAbsolute fn)
                                                         Nothing -> return Nothing
                                           sendHighlighting [(nfc, AnnNamespace ns srcFnAbs)])
                        [(re, fn, ns, nfc) | ImportInfo re fn _ ns _ nfc <- imports]
                  reportParserWarnings
                  sendParserHighlighting

                  -- process and check module aliases
                  let modAliases = M.fromList
                        [ (prep alias, prep realName)
                        | ImportInfo { import_reexport = reexport
                                     , import_path = realName
                                     , import_rename = Just (alias, _)
                                     , import_location = fc } <- imports
                        ]
                      prep = map T.pack . reverse . Spl.splitOn [pathSeparator]
                      aliasNames = [ (alias, fc)
                                   | ImportInfo { import_rename = Just (alias, _)
                                                , import_location = fc } <- imports
                                   ]
                      histogram = groupBy ((==) `on` fst) . sortBy (comparing fst) $ aliasNames
                  case map head . filter ((/= 1) . length) $ histogram of
                    []       -> logParser 3 $ "Module aliases: " ++ show (M.toList modAliases)
                    (n,fc):_ -> throwError . At fc . Msg $ "import alias not unique: " ++ show n

                  i <- getIState
                  putIState (i { default_access = Private, module_aliases = modAliases })
                  clearIBC -- start a new .ibc file
                  -- record package info in .ibc
                  imps <- allImportDirs
                  mapM_ addIBC (map IBCImportDir imps)
                  mapM_ (addIBC . IBCImport)
                    [ (reexport, realName)
                    | ImportInfo { import_reexport = reexport
                                 , import_path = realName
                                 } <- imports
                    ]
                  let syntax = defaultSyntax{ syn_namespace = reverse mname,
                                              maxline = toline }
                  ist <- getIState
                  -- Save the span from parsing the module header, because
                  -- an empty program parse might obliterate it.
                  let oldSpan = idris_parsedSpan ist
                  ds' <- parseProg syntax f file pos

                  case (ds', oldSpan) of
                    ([], Just fc) ->
                      -- If no program elements were parsed, we dind't
                      -- get a loaded region in the IBC file. That
                      -- means we need to add it back.
                      do ist <- getIState
                         putIState ist { idris_parsedSpan = oldSpan
                                       , ibc_write = IBCParsedRegion fc :
                                                     ibc_write ist
                                       }
                    _ -> return ()
                  sendParserHighlighting

                  -- Parsing done, now process declarations

                  let ds = namespaces mname ds'
                  logParser 3 (show $ showDecls verbosePPOption ds)
                  i <- getIState
                  logLvl 10 (show (toAlist (idris_implicits i)))
                  logLvl 3 (show (idris_infixes i))
                  -- Now add all the declarations to the context
                  iReport 1 $ "Type checking " ++ f
                  -- we totality check after every Mutual block, so if
                  -- anything is a single definition, wrap it in a
                  -- mutual block on its own
                  elabDecls (toplevelWith f) (map toMutual ds)
                  i <- getIState
                  -- simplify every definition do give the totality checker
                  -- a better chance
                  mapM_ (\n -> do logLvl 5 $ "Simplifying " ++ show n
                                  ctxt' <-
                                    do ctxt <- getContext
                                       tclift $ simplifyCasedef n [] [] (getErasureInfo i) ctxt
                                  setContext ctxt')
                           (map snd (idris_totcheck i))
                  -- build size change graph from simplified definitions
                  iReport 3 $ "Totality checking " ++ f
                  logLvl 1 $ "Totality checking " ++ f
                  i <- getIState
                  mapM_ buildSCG (idris_totcheck i)
                  mapM_ checkDeclTotality (idris_totcheck i)
                  mapM_ verifyTotality (idris_totcheck i)

                  -- Redo totality check for deferred names
                  let deftots = idris_defertotcheck i
                  logLvl 2 $ "Totality checking " ++ show deftots
                  mapM_ (\x -> do tot <- getTotality x
                                  case tot of
                                       Total _ ->
                                         do let opts = case lookupCtxtExact x (idris_flags i) of
                                                          Just os -> os
                                                          Nothing -> []
                                            when (AssertTotal `notElem` opts) $
                                                setTotality x Unchecked
                                       _ -> return ()) (map snd deftots)
                  mapM_ buildSCG deftots
                  mapM_ checkDeclTotality deftots

                  logLvl 1 ("Finished " ++ f)
                  ibcsd <- valIBCSubDir i
                  logLvl  1 $ "Universe checking " ++ f
                  iReport 3 $ "Universe checking " ++ f
                  iucheck
                  let ibc = ibcPathNoFallback ibcsd f
                  i <- getIState
                  addHides (hide_list i)

                  -- Save module documentation if applicable
                  i <- getIState
                  case mdocs of
                    Nothing   -> return ()
                    Just docs -> addModDoc syntax mname docs


                  -- Finally, write an ibc and highlights if checking was successful
                  ok <- noErrors
                  when ok $
                    do idrisCatch (do writeIBC f ibc; clearIBC)
                                  (\c -> return ()) -- failure is harmless
                       hl <- getDumpHighlighting
                       when hl $
                         idrisCatch (writeHighlights f)
                                    (const $ return ()) -- failure is harmless
                  clearHighlights
                  i <- getIState
                  putIState (i { default_total = def_total,
                                 hide_list = emptyContext })
                  return ()
  where
    namespaces :: [String] -> [PDecl] -> [PDecl]
    namespaces []     ds = ds
    namespaces (x:xs) ds = [PNamespace x NoFC (namespaces xs ds)]

    toMutual :: PDecl -> PDecl
    toMutual m@(PMutual _ d) = m
    toMutual (PNamespace x fc ds) = PNamespace x fc (map toMutual ds)
    toMutual x = let r = PMutual (fileFC "single mutual") [x] in
                 case x of
                   PClauses{} -> r
                   PInterface{} -> r
                   PData{} -> r
                   PImplementation{} -> r
                   _ -> x

    addModDoc :: SyntaxInfo -> [String] -> Docstring () -> Idris ()
    addModDoc syn mname docs =
      do ist <- getIState
         docs' <- elabDocTerms (toplevelWith f) (parsedDocs ist)
         let modDocs' = addDef docName docs' (idris_moduledocs ist)
         putIState ist { idris_moduledocs = modDocs' }
         addIBC (IBCModDocs docName)
      where
        docName = NS modDocName (map T.pack (reverse mname))
        parsedDocs ist = annotCode (tryFullExpr syn ist) docs

{-| Adds names to hide list -}
addHides :: Ctxt Accessibility -> Idris ()
addHides xs = do i <- getIState
                 let defh = default_access i
                 mapM_ doHide (toAlist xs)
  where doHide (n, a) = do setAccessibility n a
                           addIBC (IBCAccess n a)

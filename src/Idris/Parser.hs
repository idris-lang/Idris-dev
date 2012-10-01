{-# LANGUAGE PatternGuards #-}

module Idris.Parser where

import Idris.AbsSyntax
import Idris.DSL
import Idris.Imports
import Idris.Error
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Coverage
import Idris.IBC
import Idris.Unlit
import Paths_idris

import Core.CoreParser
import Core.TT
import Core.Evaluate

import Text.Parsec
import Text.Parsec.Error
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import qualified Text.Parsec.Token as PTok

import Data.List
import Control.Monad.State
import Debug.Trace
import Data.Maybe
import System.FilePath

type TokenParser a = PTok.TokenParser a

type IParser = GenParser Char IState

lexer :: TokenParser IState
lexer  = PTok.makeTokenParser idrisDef

whiteSpace = PTok.whiteSpace lexer
lexeme     = PTok.lexeme lexer
symbol     = PTok.symbol lexer
natural    = PTok.natural lexer
parens     = PTok.parens lexer
semi       = PTok.semi lexer
comma      = PTok.comma lexer
identifier = PTok.identifier lexer
reserved   = PTok.reserved lexer
operator   = PTok.operator lexer
reservedOp = PTok.reservedOp lexer
integer    = PTok.integer lexer
float      = PTok.float lexer
strlit     = PTok.stringLiteral lexer
chlit      = PTok.charLiteral lexer
lchar      = lexeme.char

-- Loading modules

loadModule :: FilePath -> Idris String
loadModule f 
   = idrisCatch (do i <- getIState
                    ibcsd <- valIBCSubDir i
                    ids <- allImportDirs i
                    fp <- liftIO $ findImport ids ibcsd f
                    if f `elem` imported i
                       then iLOG $ "Already read " ++ f
                       else do putIState (i { imported = f : imported i })
                               case fp of
                                   IDR fn  -> loadSource False fn
                                   LIDR fn -> loadSource True  fn
                                   IBC fn src -> 
                                     idrisCatch (loadIBC fn)
                                                (\c -> do iLOG $ fn ++ " failed " ++ show c
                                                          case src of
                                                            IDR sfn -> loadSource False sfn
                                                            LIDR sfn -> loadSource True sfn)
                    let (dir, fh) = splitFileName f
                    return (dropExtension fh))
                (\e -> do let msg = show e
                          setErrLine (getErrLine msg)
                          iputStrLn msg
                          return "")

loadSource :: Bool -> FilePath -> Idris () 
loadSource lidr f 
             = do iLOG ("Reading " ++ f)
                  file_in <- liftIO $ readFile f
                  file <- if lidr then tclift $ unlit f file_in else return file_in
                  (mname, modules, rest, pos) <- parseImports f file
                  i <- getIState
                  putIState (i { default_access = Hidden })
                  mapM_ loadModule modules
                  clearIBC -- start a new .ibc file
                  mapM_ (addIBC . IBCImport) modules
                  ds' <- parseProg (defaultSyntax {syn_namespace = reverse mname }) 
                                   f rest pos
                  let ds = namespaces mname ds'
                  logLvl 3 (dumpDecls ds)
                  i <- getIState
                  logLvl 10 (show (toAlist (idris_implicits i)))
                  logLvl 3 (show (idris_infixes i))
                  -- Now add all the declarations to the context
                  v <- verbose
                  when v $ iputStrLn $ "Type checking " ++ f
                  mapM_ (elabDecl toplevel) ds
                  i <- get
                  mapM_ checkDeclTotality (idris_totcheck i)
                  iLOG ("Finished " ++ f)
                  ibcsd <- valIBCSubDir i
                  let ibc = ibcPathNoFallback ibcsd f
                  iucheck
                  i <- getIState
                  addHides (hide_list i)
                  ok <- noErrors
                  when ok $
                    idrisCatch (do writeIBC f ibc; clearIBC)
                               (\c -> return ()) -- failure is harmless
                  i <- getIState
                  putIState (i { hide_list = [] })
                  return ()
  where
    namespaces []     ds = ds
    namespaces (x:xs) ds = [PNamespace x (namespaces xs ds)]

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

parseExpr i = runParser (pFullExpr defaultSyntax) i "(input)"
parseTac i = runParser (do t <- pTactic defaultSyntax
                           eof
                           return t) i "(proof)"

iShowError fname err = let ln  = sourceLine (errorPos err)
                           clm = sourceColumn (errorPos err)
                           msg = map messageString (errorMessages err) in
                           fname ++ ":" ++ show ln ++ ":parse error"
                                 ++ " at column " ++ show clm -- ++ " with error:\n\t" ++ show msg

parseImports :: FilePath -> String -> Idris ([String], [String], String, SourcePos)
parseImports fname input 
    = do i <- get
         case runParser (do whiteSpace
                            mname <- pHeader
                            ps    <- many pImport
                            rest  <- getInput
                            pos   <- getPosition
                            return ((mname, ps, rest, pos), i)) i fname input of
              Left err     -> fail (iShowError fname err)
              Right (x, i) -> do put i
                                 return x

pHeader :: IParser [String]
pHeader = try (do reserved "module"; i <- identifier; option ';' (lchar ';')
                  return (parseName i))
     <|> return []
  where parseName x = case span (/='.') x of
                           (x, "")    -> [x]
                           (x, '.':y) -> x : parseName y

pushIndent :: IParser ()
pushIndent = do pos <- getPosition
                ist <- getState
                setState (ist { indent_stack = sourceColumn pos :
                                                indent_stack ist })

lastIndent :: IParser Int
lastIndent = do ist <- getState
                case indent_stack ist of
                     (x : xs) -> return x
                     _        -> return 1

indent :: IParser Int
indent = liftM sourceColumn getPosition

popIndent :: IParser ()
popIndent = do ist <- getState
               let (x : xs) = indent_stack ist
               setState (ist { indent_stack = xs })

openBlock :: IParser ()
openBlock = do lchar '{'
               ist <- getState
               setState (ist { brace_stack = Nothing : brace_stack ist })
         <|> do ist <- getState
                lvl <- indent
                setState (ist { brace_stack = Just lvl : brace_stack ist })

closeBlock :: IParser ()
closeBlock = do ist <- getState
                bs <- case brace_stack ist of
                        Nothing : xs -> do lchar '}'
                                           return xs
                        Just lvl : xs -> do i   <- indent
                                            inp <- getInput
--                                              trace (show (take 10 inp, i, lvl)) $
                                            if i >= lvl && take 1 inp /= ")" 
                                               then fail "Not end of block"
                                               else return xs
                setState (ist { brace_stack = bs })

pTerminator = do lchar ';'; popIndent
          <|> do c <- indent; l <- lastIndent
                 if c <= l 
                    then popIndent
                    else fail "Not a terminator"
          <|> do i <- getInput
                 if "}" `isPrefixOf` i || ")" `isPrefixOf` i
                    then popIndent 
                    else fail "Not a terminator"
          <|> lookAhead eof

pBarTerminator 
            = do lchar '|'; return ()
          <|> do c <- indent; l <- lastIndent
                 unless (c <= l) $ fail "Not a terminator"
          <|> lookAhead eof

pKeepTerminator 
            = do lchar ';'; return ()
          <|> do c <- indent; l <- lastIndent
                 unless (c <= l) $ fail "Not a terminator"
          <|> do i <- getInput
                 let h = take 1 i
                 unless (h `elem` ["}", ")", "|"]) $ fail "Not a terminator"
          <|> lookAhead eof

notEndApp = do c <- indent; l <- lastIndent
               i <- getInput
               when (c <= l) $ fail "Terminator"

notEndBlock = do ist <- getState
                 case brace_stack ist of
                    Just lvl : xs -> do i   <- indent
                                        inp <- getInput
                                        when (i < lvl || ")" `isPrefixOf` inp) $ fail "End of block"
                    _             -> return ()

pfc :: IParser FC
pfc = do s <- getPosition
         let (dir, file) = splitFileName (sourceName s)
         let f = case dir of
                      "./" -> file
                      _    -> sourceName s
         return $ FC f (sourceLine s)

pImport :: IParser String
pImport = do reserved "import"; f <- identifier; option ';' (lchar ';')
             return (map dot f)
  where dot '.' = '/'
        dot c = c

parseProg :: SyntaxInfo -> FilePath -> String -> SourcePos -> Idris [PDecl]
parseProg syn fname input pos
    = do i <- get
         case runParser (do setPosition pos
                            whiteSpace
                            ps <- many (pDecl syn)
                            eof
                            i' <- getState
                            return (concat ps, i')) i fname input of
            Left err     -> fail (iShowError fname err)
            Right (x, i) -> do put i
                               return (collect x)

-- Collect PClauses with the same function name

collect :: [PDecl] -> [PDecl]
collect (c@(PClauses _ o _ _) : ds) 
    = clauses (cname c) [] (c : ds)
  where clauses n acc (PClauses fc _ _ [PClause fc' n' l ws r w] : ds)
           | n == n' = clauses n (PClause fc' n' l ws r (collect w) : acc) ds
        clauses n acc (PClauses fc _ _ [PWith fc' n' l ws r w] : ds)
           | n == n' = clauses n (PWith fc' n' l ws r (collect w) : acc) ds
        clauses n acc xs = PClauses (getfc c) o n (reverse acc) : collect xs

        cname (PClauses fc _ _ [PClause _ n _ _ _ _]) = n
        cname (PClauses fc _ _ [PWith   _ n _ _ _ _]) = n
        getfc (PClauses fc _ _ _) = fc

collect (PParams f ns ps : ds) = PParams f ns (collect ps) : collect ds
collect (PNamespace ns ps : ds) = PNamespace ns (collect ps) : collect ds
collect (PClass f s cs n ps ds : ds') = PClass f s cs n ps (collect ds) : collect ds'
collect (PInstance f s cs n ps t en ds : ds') 
    = PInstance f s cs n ps t en (collect ds) : collect ds'
collect (d : ds) = d : collect ds
collect [] = []

pFullExpr :: SyntaxInfo -> IParser PTerm
pFullExpr syn 
          = do x <- pExpr syn; eof;
               i <- getState
               return $ desugar syn i x

pDecl :: SyntaxInfo -> IParser [PDecl]
pDecl syn = do notEndBlock
               pDeclBody where
  pDeclBody
      = do d <- pDecl' syn
           i <- getState
           let d' = fmap (desugar syn i) d
           return [d']
    <|> pUsing syn
    <|> pParams syn
    <|> pNamespace syn
    <|> pClass syn
    <|> pInstance syn
    <|> do d <- pDSL syn; return [d]
    <|> pDirective
    <|> try (do reserved "import"; fp <- identifier
                fail "imports must be at the top of file") 

pFunDecl :: SyntaxInfo -> IParser [PDecl]
pFunDecl syn
      = try (do notEndBlock
                d <- pFunDecl' syn
                i <- getState
                let d' = fmap (desugar syn i) d
                return [d'])

--------- Top Level Declarations ---------

pDecl' :: SyntaxInfo -> IParser PDecl
pDecl' syn
       = try pFixity
     <|> pFunDecl' syn
     <|> try (pData syn)
     <|> try (pRecord syn)
     <|> pSyntaxDecl syn

pSyntaxDecl :: SyntaxInfo -> IParser PDecl
pSyntaxDecl syn
    = do s <- pSyntaxRule syn
         i <- getState
         let rs = syntax_rules i
         let ns = syntax_keywords i
         let ibc = ibc_write i
         let ks = map show (names s)
         setState (i { syntax_rules = s : rs,
                       syntax_keywords = ks ++ ns,
                       ibc_write = IBCSyntax s : map IBCKeyword ks ++ ibc
                     })
         fc <- pfc
         return (PSyntax fc s)
  where
    names (Rule syms _ _) = mapMaybe ename syms
    ename (Keyword n) = Just n
    ename _ = Nothing

pSyntaxRule :: SyntaxInfo -> IParser Syntax
pSyntaxRule syn 
    = do pushIndent
         sty <- option AnySyntax (do reserved "term"; return TermSyntax
                                  <|> do reserved "pattern"; return PatternSyntax)
         reserved "syntax"
         syms <- many1 pSynSym
         when (all expr syms) $ fail "No keywords in syntax rule"
         let ns = mapMaybe name syms
         when (length ns /= length (nub ns)) 
            $ fail "Repeated variable in syntax rule"
         lchar '='
         tm <- pExpr (impOK syn)
         pTerminator
         return (Rule (mkSimple syms) tm sty)
  where
    expr (Expr _) = True
    expr _ = False
    name (Expr n) = Just n
    name _ = Nothing

    -- Can't parse two full expressions (i.e. expressions with application) in a row
    -- so change the first to a simple expression

    mkSimple (Expr e : es) = SimpleExpr e : mkSimple' es
    mkSimple xs = mkSimple' xs

    mkSimple' (Expr e : Expr e1 : es) = SimpleExpr e : mkSimple' (Expr e1 : es)
    mkSimple' (e : es) = e : mkSimple' es
    mkSimple' [] = []

pSynSym :: IParser SSymbol
pSynSym = try (do lchar '['; n <- pName; lchar ']'
                  return (Expr n))
      <|> try (do lchar '{'; n <- pName; lchar '}'
                  return (Binding n))
      <|> do n <- iName []
             return (Keyword n)
      <|> do sym <- strlit
             return (Symbol sym)

pFunDecl' :: SyntaxInfo -> IParser PDecl
pFunDecl' syn = try (do pushIndent
                        opts <- pFnOpts
                        acc <- pAccessibility
                        opts' <- pFnOpts
                        n_in <- pfName
                        let n = expandNS syn n_in
                        ty <- pTSig (impOK syn)
                        fc <- pfc
                        pTerminator 
--                         ty' <- implicit syn n ty
                        addAcc n acc
                        return (PTy syn fc (opts ++ opts') n ty))
            <|> try (pPattern syn)
            <|> try (pCAF syn)

pUsing :: SyntaxInfo -> IParser [PDecl]
pUsing syn = 
    do reserved "using"; lchar '('; ns <- tyDeclList syn; lchar ')'
       openBlock
       let uvars = using syn
       ds <- many1 (pDecl (syn { using = uvars ++ ns }))
       closeBlock
       return (concat ds)

pParams :: SyntaxInfo -> IParser [PDecl]
pParams syn = 
    do reserved "params"; lchar '('; ns <- tyDeclList syn; lchar ')'
       lchar '{'
       let pvars = syn_params syn
       ds <- many1 (pDecl syn { syn_params = pvars ++ ns })
       lchar '}'
       fc <- pfc
       return [PParams fc ns (concat ds)]

pNamespace :: SyntaxInfo -> IParser [PDecl]
pNamespace syn =
    do reserved "namespace"; n <- identifier;
       openBlock 
       ds <- many1 (pDecl syn { syn_namespace = n : syn_namespace syn })
       closeBlock
       return [PNamespace n (concat ds)] 

--------- Fixity ---------

pFixity :: IParser PDecl
pFixity = do pushIndent
             f <- fixity; i <- natural; ops <- sepBy1 operator (lchar ',')
             pTerminator 
             let prec = fromInteger i
             istate <- getState
             let fs = map (Fix (f prec)) ops
             setState (istate { 
                idris_infixes = nub $ sort (fs ++ idris_infixes istate),
                ibc_write = map IBCFix fs ++ ibc_write istate })
             fc <- pfc
             return (PFix fc (f prec) ops)

fixity :: IParser (Int -> Fixity) 
fixity = try (do reserved "infixl"; return Infixl)
     <|> try (do reserved "infixr"; return Infixr)
     <|> try (do reserved "infix";  return InfixN)
     <|> try (do reserved "prefix"; return PrefixN)

--------- Type classes ---------

pClass :: SyntaxInfo -> IParser [PDecl]
pClass syn = do acc <- pAccessibility
                reserved "class"; fc <- pfc; cons <- pConstList syn; n_in <- pName
                let n = expandNS syn n_in
                cs <- many1 carg
                reserved "where"; openBlock 
                ds <- many $ pFunDecl syn
                closeBlock
                let allDs = concat ds
                accData acc n (concatMap declared allDs)
                return [PClass syn fc cons n cs allDs]
  where
    carg = do lchar '('; i <- pName; lchar ':'; ty <- pExpr syn; lchar ')'
              return (i, ty)
       <|> do i <- pName;
              return (i, PSet)

pInstance :: SyntaxInfo -> IParser [PDecl]
pInstance syn = do reserved "instance"; fc <- pfc
                   en <- option Nothing
                            (do lchar '['; n_in <- pfName; lchar ']'
                                let n = expandNS syn n_in
                                return (Just n))
                   cs <- pConstList syn
                   cn <- pName
                   args <- many1 (pSimpleExpr syn)
                   let sc = PApp fc (PRef fc cn) (map pexp args)
                   let t = bindList (PPi constraint) (map (\x -> (MN 0 "c", x)) cs) sc
                   reserved "where"; openBlock 
                   ds <- many $ pFunDecl syn
                   closeBlock
                   return [PInstance syn fc cs cn args t en (concat ds)]

--------- Expressions ---------

pExpr syn = do i <- getState
               buildExpressionParser (table (idris_infixes i)) (pExpr' syn)

pExpr' :: SyntaxInfo -> IParser PTerm
pExpr' syn 
       = try (pExtExpr syn)
     <|> pNoExtExpr syn

pExtExpr :: SyntaxInfo -> IParser PTerm
pExtExpr syn = do i <- getState
                  pExtensions syn (syntax_rules i)

pSimpleExtExpr :: SyntaxInfo -> IParser PTerm
pSimpleExtExpr syn = do i <- getState
                        pExtensions syn (filter simple (syntax_rules i))
  where
    simple (Rule (Expr x:xs) _ _) = False
    simple (Rule (SimpleExpr x:xs) _ _) = False
    simple (Rule [Keyword _] _ _) = True
    simple (Rule [Symbol _]  _ _) = True
    simple (Rule (_:xs) _ _) = case last xs of
        Keyword _ -> True
        Symbol _  -> True
        _ -> False
    simple _ = False

pNoExtExpr syn =
         try (pApp syn) 
     <|> pRecordSet syn
     <|> try (pSimpleExpr syn)
     <|> pLambda syn
     <|> pLet syn
     <|> pPi syn 
     <|> pDoBlock syn
     <|> pComprehension syn
    
pExtensions :: SyntaxInfo -> [Syntax] -> IParser PTerm
pExtensions syn rules = choice (map (try . pExt syn) (filter valid rules))
  where
    valid (Rule _ _ AnySyntax) = True
    valid (Rule _ _ PatternSyntax) = inPattern syn
    valid (Rule _ _ TermSyntax) = not (inPattern syn)


data SynMatch = SynTm PTerm | SynBind Name

pExt :: SyntaxInfo -> Syntax -> IParser PTerm
pExt syn (Rule ssym ptm _)
    = do smap <- mapM pSymbol ssym
         let ns = mapMaybe id smap
         return (update ns ptm) -- updated with smap
  where
    pSymbol (Keyword n)    = do reserved (show n); return Nothing
    pSymbol (Expr n)       = do tm <- pExpr syn
                                return $ Just (n, SynTm tm)
    pSymbol (SimpleExpr n) = do tm <- pSimpleExpr syn
                                return $ Just (n, SynTm tm)
    pSymbol (Binding n)    = do b <- pName
                                return $ Just (n, SynBind b)
    pSymbol (Symbol s)     = do symbol s
                                return Nothing
    dropn n [] = []
    dropn n ((x,t) : xs) | n == x = xs
                         | otherwise = (x,t):dropn n xs

    updateB ns n = case lookup n ns of
                     Just (SynBind t) -> t
                     _ -> n

    update ns (PRef fc n) = case lookup n ns of
                              Just (SynTm t) -> t
                              _ -> PRef fc n
    update ns (PLam n ty sc) = PLam (updateB ns n) (update ns ty) (update (dropn n ns) sc)
    update ns (PPi p n ty sc) = PPi p (updateB ns n) (update ns ty) (update (dropn n ns) sc) 
    update ns (PLet n ty val sc) = PLet (updateB ns n) (update ns ty) (update ns val)
                                          (update (dropn n ns) sc)
    update ns (PApp fc t args) = PApp fc (update ns t) (map (fmap (update ns)) args)
    update ns (PCase fc c opts) = PCase fc (update ns c) (map (pmap (update ns)) opts) 
    update ns (PPair fc l r) = PPair fc (update ns l) (update ns r)
    update ns (PDPair fc l t r) = PDPair fc (update ns l) (update ns t) (update ns r)
    update ns (PAlternative a as) = PAlternative a (map (update ns) as)
    update ns (PHidden t) = PHidden (update ns t)
    update ns (PDoBlock ds) = PDoBlock $ upd ns ds
      where upd ns (DoExp fc t : ds) = DoExp fc (update ns t) : upd ns ds
            upd ns (DoBind fc n t : ds) = DoBind fc n (update ns t) : upd (dropn n ns) ds
            upd ns (DoLet fc n ty t : ds) = DoLet fc n (update ns ty) (update ns t) 
                                                : upd (dropn n ns) ds
            upd ns (DoBindP fc i t : ds) = DoBindP fc (update ns i) (update ns t) 
                                                : upd ns ds
            upd ns (DoLetP fc i t : ds) = DoLetP fc (update ns i) (update ns t) 
                                                : upd ns ds
    update ns t = t

pName = do i <- getState
           iName (syntax_keywords i)
    <|> do reserved "instance"
           i <- getState
           UN n <- iName (syntax_keywords i)
           return (UN ('@':n))

-- Parser for an operator in function position, i.e. enclosed by `()', with an
-- optional namespace.
pOpFront = maybeWithNS pOpFrontNoNS False []
  where pOpFrontNoNS = do lchar '('; o <- operator; lchar ')'; return o

pfName = try pOpFront
         <|> pName

pAccessibility' :: IParser Accessibility
pAccessibility'
        = do reserved "public";   return Public
      <|> do reserved "abstract"; return Frozen
      <|> do reserved "private";  return Hidden

pAccessibility :: IParser (Maybe Accessibility)
pAccessibility
        = do acc <- pAccessibility'; return (Just acc)
      <|> return Nothing

pFnOpts :: IParser [FnOpt]
pFnOpts = do reserved "total"; xs <- pFnOpts; return (TotalFn : xs)
      <|> try (do lchar '%'; reserved "export"; c <- strlit; xs <- pFnOpts
                  return (CExport c : xs))
      <|> do lchar '%'; reserved "assert_total"; xs <- pFnOpts; return (AssertTotal : xs)
      <|> do lchar '%'; reserved "specialise"; 
             lchar '['; ns <- sepBy pfName (lchar ','); lchar ']'
             xs <- pFnOpts
             return (Specialise ns : xs)
      <|> return []

addAcc :: Name -> Maybe Accessibility -> IParser ()
addAcc n a = do i <- getState
                setState (i { hide_list = (n, a) : hide_list i })

pCaseExpr syn = do
  reserved "case"; fc <- pfc; scr <- pExpr syn; reserved "of";
  openBlock 
  pushIndent
  opts <- many1 (do notEndBlock
                    x <- pCaseOpt syn
                    pKeepTerminator
                    return x) -- sepBy1 (pCaseOpt syn) (lchar '|')
  popIndent
  closeBlock
  return (PCase fc scr opts)

pProofExpr syn = do
  reserved "proof"; lchar '{'
  ts <- endBy (pTactic syn) (lchar ';')
  lchar '}'
  return (PProof ts)

pTacticsExpr syn = do
  reserved "tactics"; lchar '{'
  ts <- endBy (pTactic syn) (lchar ';')
  lchar '}'
  return (PTactics ts)

pSimpleExpr syn = 
        try (do symbol "!["; t <- pTerm; lchar ']'; return $ PQuote t)
        <|> do lchar '?'; x <- pName; return (PMetavar x)
        <|> do reserved "refl"; fc <- pfc; return (PRefl fc)
--         <|> do reserved "return"; fc <- pfc; return (PReturn fc)
        <|> pProofExpr syn 
        <|> pTacticsExpr syn
        <|> pCaseExpr syn
        <|> try (do x <- pfName
                    fc <- pfc
                    return (PRef fc x))
        <|> try (pList syn)
        <|> try (pAlt syn)
        <|> try (pIdiom syn)
        <|> try (do lchar '('
                    bracketed (noImp syn))
        <|> try (do c <- pConstant
                    fc <- pfc
                    return (modifyConst syn fc (PConstant c)))
        <|> do reserved "Set"; return PSet
        <|> try (do symbol "()"
                    fc <- pfc
                    return (PTrue fc))
        <|> try (do symbol "_|_"
                    fc <- pfc
                    return (PFalse fc))
        <|> do lchar '_'; return Placeholder
        <|> pSimpleExtExpr syn

bracketed syn =
            try (pPair syn)
        <|> try (do e <- pExpr syn; lchar ')'; return e)
--         <|> try (do reserved "typed"
--                     e <- pExpr syn; symbol ":"; t <- pExpr syn; lchar ')'
--                     return (PTyped e t))
        <|> try (do fc <- pfc; o <- operator; e <- pExpr syn; lchar ')'
                    return $ PLam (MN 0 "x") Placeholder
                                  (PApp fc (PRef fc (UN o)) [pexp (PRef fc (MN 0 "x")), 
                                                             pexp e]))
        <|> try (do fc <- pfc; e <- pSimpleExpr syn; o <- operator; lchar ')'
                    return $ PLam (MN 0 "x") Placeholder
                                  (PApp fc (PRef fc (UN o)) [pexp e,
                                                             pexp (PRef fc (MN 0 "x"))]))

pCaseOpt :: SyntaxInfo -> IParser (PTerm, PTerm)
pCaseOpt syn = do lhs <- pExpr syn; symbol "=>"; rhs <- pExpr syn
                  return (lhs, rhs)

modifyConst :: SyntaxInfo -> FC -> PTerm -> PTerm
modifyConst syn fc (PConstant (I x)) 
    | not (inPattern syn)
        = PApp fc (PRef fc (UN "fromInteger")) [pexp (PConstant (I x))]
    | otherwise = PConstant (I x)
modifyConst syn fc x = x

pList syn = do lchar '['; fc <- pfc; xs <- sepBy (pExpr syn) (lchar ','); lchar ']'
               return (mkList fc xs)
  where
    mkList fc [] = PRef fc (UN "Nil")
    mkList fc (x : xs) = PApp fc (PRef fc (UN "::")) [pexp x, pexp (mkList fc xs)] 

pPair syn = try (do l <- pExpr syn 
                    fc <- pfc
                    rest <- restTuple 
                    case rest of
                        [] -> return l
                        [Left r] -> return (PPair fc l r)
                        [Right r] -> return (PDPair fc l Placeholder r))
        <|> try (do x <- ntuple
                    lchar ')'
                    return x) 
        <|> do ln <- pName; lchar ':'
               lty <- pExpr syn
               reservedOp "**"
               fc <- pfc
               r <- pExpr syn
               lchar ')'
               return (PDPair fc (PRef fc ln) lty r) 
  where
    restTuple = do lchar ')'; return []
            <|> do lchar ','
                   r <- pExpr syn
                   lchar ')'
                   return [Left r]
            <|> do reservedOp "**"
                   r <- pExpr syn
                   lchar ')'
                   return [Right r]
    ntuple = try (do l <- pExpr syn; fc <- pfc; lchar ','
                     rest <- ntuple
                     return (PPair fc l rest))
             <|> (do l <- pExpr syn; fc <- pfc; lchar ','
                     r <- pExpr syn
                     return (PPair fc l r))
       
pAlt syn = do symbol "(|"; alts <- sepBy1 (pExpr' syn) (lchar ','); symbol "|)"
              return (PAlternative False alts)

pHSimpleExpr syn
             = do lchar '.'
                  e <- pSimpleExpr syn
                  return $ PHidden e
           <|> pSimpleExpr syn

pApp syn = do f <- pSimpleExpr syn
              fc <- pfc
              args <- many1 (do notEndApp
                                pArg syn)
              i <- getState
              return (dslify i $ PApp fc f args)
  where
    dslify i (PApp fc (PRef _ f) [a])
        | [d] <- lookupCtxt Nothing f (idris_dsls i)
            = desugar (syn { dsl_info = d }) i (getTm a)
    dslify i t = t

pArg :: SyntaxInfo -> IParser PArg
pArg syn = try (pImplicitArg syn)
       <|> try (pConstraintArg syn)
       <|> do e <- pSimpleExpr syn
              return (pexp e)

pImplicitArg syn = do lchar '{'
                      n <- pName
                      fc <- pfc
                      v <- option (PRef fc n) (do lchar '='
                                                  pExpr syn)
                      lchar '}'
                      return (pimp n v)

pConstraintArg syn = do symbol "@{"
                        e <- pExpr syn
                        symbol "}"
                        return (pconst e)

pRecordSet syn 
    = do reserved "record"
         lchar '{'
         fields <- sepBy1 pFieldSet (lchar ',')
         lchar '}'
         fc <- pfc
         rec <- option Nothing (do e <- pSimpleExpr syn
                                   return (Just e))
         case rec of
            Nothing ->
                return (PLam (MN 0 "fldx") Placeholder
                            (applyAll fc fields (PRef fc (MN 0 "fldx"))))
            Just v -> return (applyAll fc fields v)
   where pFieldSet = do n <- pfName
                        lchar '='
                        e <- pExpr syn
                        return (n, e)
         applyAll fc [] x = x
         applyAll fc ((n, e) : es) x
            = applyAll fc es (PApp fc (PRef fc (mkSet n)) [pexp e, pexp x])
                        
mkSet (UN n) = UN ("set_" ++ n)
mkSet (MN 0 n) = MN 0 ("set_" ++ n)
mkSet (NS n s) = NS (mkSet n) s

noImp syn = syn { implicitAllowed = False }
impOK syn = syn { implicitAllowed = True }

pTSig syn = do lchar ':'
               cs <- if implicitAllowed syn then pConstList syn else return []
               sc <- pExpr syn 
               return (bindList (PPi constraint) (map (\x -> (MN 0 "c", x)) cs) sc)

pLambda syn = do lchar '\\'
                 try (do xt <- tyOptDeclList syn
                         symbol "=>"
                         sc <- pExpr syn
                         return (bindList PLam xt sc)
                  <|> (do ps <- sepBy (do fc <- pfc
                                          e <- pSimpleExpr syn
                                          return (fc, e)) (lchar ',')
                          symbol "=>"
                          sc <- pExpr syn
                          return (pmList (zip [0..] ps) sc)))
    where pmList [] sc = sc
          pmList ((i, (fc, x)) : xs) sc 
                = PLam (MN i "lamp") Placeholder
                        (PCase fc (PRef fc (MN i "lamp"))
                                [(x, pmList xs sc)])

pLet syn = try (do reserved "let"; n <- pName; 
                   ty <- option Placeholder (do lchar ':'; pExpr' syn)
                   lchar '='
                   v <- pExpr syn
                   reserved "in";  sc <- pExpr syn
                   return (PLet n ty v sc))
           <|> (do reserved "let"; fc <- pfc; pat <- pExpr' (syn { inPattern = True } )
                   symbol "="; v <- pExpr syn
                   reserved "in"; sc <- pExpr syn
                   return (PCase fc v [(pat, sc)]))

pPi syn = 
     try (do lazy <- option False (do lchar '|'; return True)
             st <- pStatic
             lchar '('; xt <- tyDeclList syn; lchar ')'
             symbol "->"
             sc <- pExpr syn
             return (bindList (PPi (Exp lazy st)) xt sc))
 <|> try (if implicitAllowed syn 
             then do lazy <- option False (do lchar '|'
                                              return True)
                     st <- pStatic
                     lchar '{'
                     xt <- tyDeclList syn
                     lchar '}'
                     symbol "->"
                     sc <- pExpr syn
                     return (bindList (PPi (Imp lazy st)) xt sc)
             else fail "No implicit arguments allowed here")
 <|> try (do lchar '{'
             reserved "auto"
             xt <- tyDeclList syn
             lchar '}'
             symbol "->"
             sc <- pExpr syn
             return (bindList (PPi (TacImp False Dynamic (PTactics [Trivial]))) xt sc))
 <|> try (do lchar '{'
             reserved "default"
             script <- pSimpleExpr syn 
             xt <- tyDeclList syn
             lchar '}'
             symbol "->"
             sc <- pExpr syn
             return (bindList (PPi (TacImp False Dynamic script)) xt sc))
      <|> do --lazy <- option False (do lchar '|'; return True)
             lchar '{'
             reserved "static"
             lchar '}'
             t <- pExpr' syn
             symbol "->"
             sc <- pExpr syn
             return (PPi (Exp False Static) (MN 42 "__pi_arg") t sc)

pConstList :: SyntaxInfo -> IParser [PTerm]
pConstList syn = try (do lchar '(' 
                         tys <- sepBy1 (pExpr' (noImp syn)) (lchar ',')
                         lchar ')'
                         reservedOp "=>"
                         return tys)
             <|> try (do t <- pExpr (noImp syn)
                         reservedOp "=>"
                         return [t])
             <|> return []

tyDeclList syn = try (sepBy1 (do x <- pfName
                                 t <- pTSig (noImp syn)
                                 return (x,t))
                         (lchar ','))
             <|> do ns <- sepBy1 pName (lchar ',')
                    t <- pTSig (noImp syn)
                    return (map (\x -> (x, t)) ns)

tyOptDeclList syn = sepBy1 (do x <- pfName; 
                               t <- option Placeholder (do lchar ':'
                                                           pExpr syn) 
                               return (x,t))
                           (lchar ',')

bindList b []          sc = sc
bindList b ((n, t):bs) sc = b n t (bindList b bs sc)

pComprehension syn
    = do lchar '['
         fc <- pfc
         pat <- pExpr syn
         lchar '|'
         qs <- sepBy1 (pDo syn) (lchar ',')
         lchar ']'
         return (PDoBlock (map addGuard qs ++ 
                    [DoExp fc (PApp fc (PRef fc (UN "return"))
                                 [pexp pat])]))
    where addGuard (DoExp fc e) = DoExp fc (PApp fc (PRef fc (UN "guard"))
                                                    [pexp e])
          addGuard x = x

pDoBlock syn 
    = do reserved "do"
         openBlock
         pushIndent
         ds <- many1 (do notEndBlock
                         x <- pDo syn
                         pKeepTerminator
                         return x)
         popIndent
         closeBlock
         return (PDoBlock ds)

pDo syn
     = try (do reserved "let"
               i <- pName; 
               ty <- option Placeholder (do lchar ':'
                                            pExpr' syn)
               reservedOp "="
               fc <- pfc
               e <- pExpr syn
               return (DoLet fc i ty e))
   <|> try (do reserved "let"
               i <- pExpr' syn
               reservedOp "="
               fc <- pfc
               sc <- pExpr syn
               return (DoLetP fc i sc))
   <|> try (do i <- pName
               symbol "<-"
               fc <- pfc
               e <- pExpr syn;
               return (DoBind fc i e))
   <|> try (do i <- pExpr' syn
               symbol "<-"
               fc <- pfc
               e <- pExpr syn;
               return (DoBindP fc i e))
   <|> try (do e <- pExpr syn
               fc <- pfc
               return (DoExp fc e))

pIdiom syn
    = do symbol "[|"
         fc <- pfc
         e <- pExpr syn
         symbol "|]"
         return (PIdiom fc e)

pConstant :: IParser Const
pConstant = do reserved "Integer";return BIType
        <|> do reserved "Int";    return IType
        <|> do reserved "Char";   return ChType
        <|> do reserved "Float";  return FlType
        <|> do reserved "String"; return StrType
        <|> do reserved "Ptr";    return PtrType
        <|> try (do f <- float;   return $ Fl f)
--         <|> try (do i <- natural; lchar 'L'; return $ BI i)
        <|> try (do i <- natural; return $ I (fromInteger i))
        <|> try (do s <- strlit;  return $ Str s)
        <|> try (do c <- chlit;   return $ Ch c)

pStatic :: IParser Static
pStatic = do lchar '['
             reserved "static"
             lchar ']';
             return Static
         <|> return Dynamic

table fixes 
   = [[prefix "-" (\fc x -> PApp fc (PRef fc (UN "-")) 
        [pexp (PApp fc (PRef fc (UN "fromInteger")) [pexp (PConstant (I 0))]), pexp x])]] 
       ++ toTable (reverse fixes) ++
      [[backtick],
       [binary "="  PEq AssocLeft],
       [binary "->" (\fc x y -> PPi expl (MN 42 "__pi_arg") x y) AssocRight]]

toTable fs = map (map toBin) 
                 (groupBy (\ (Fix x _) (Fix y _) -> prec x == prec y) fs)
   where toBin (Fix (PrefixN _) op) = prefix op 
                                       (\fc x -> PApp fc (PRef fc (UN op)) [pexp x])
         toBin (Fix f op) 
            = binary op (\fc x y -> PApp fc (PRef fc (UN op)) [pexp x,pexp y]) (assoc f)
         assoc (Infixl _) = AssocLeft
         assoc (Infixr _) = AssocRight
         assoc (InfixN _) = AssocNone

binary name f = Infix (do reservedOp name
                          fc <- pfc; 
                          return (f fc)) 
prefix name f = Prefix (do reservedOp name
                           fc <- pfc;
                           return (f fc))
backtick = Infix (do lchar '`'; n <- pfName
                     lchar '`'
                     fc <- pfc
                     return (\x y -> PApp fc (PRef fc n) [pexp x, pexp y])) AssocNone

--------- Data declarations ---------

-- (works for classes too - 'abstract' means the data/class is visible but members not)
accData :: Maybe Accessibility -> Name -> [Name] -> IParser ()
accData (Just Frozen) n ns = do addAcc n (Just Frozen)
                                mapM_ (\n -> addAcc n (Just Hidden)) ns
accData a n ns = do addAcc n a
                    mapM_ (`addAcc` a) ns

pRecord :: SyntaxInfo -> IParser PDecl
pRecord syn = do acc <- pAccessibility
                 reserved "record"
                 fc <- pfc
                 tyn_in <- pfName
                 ty <- pTSig (impOK syn)
                 let tyn = expandNS syn tyn_in
                 reserved "where"
                 openBlock
                 pushIndent
                 (cn, cty, _) <- pConstructor syn
                 pKeepTerminator
                 popIndent
                 closeBlock
                 accData acc tyn [cn]
                 let rsyn = syn { syn_namespace = show (nsroot tyn) : 
                                                     syn_namespace syn }
                 let fns = getRecNames rsyn cty
                 mapM_ (\n -> addAcc n (toFreeze acc)) fns
                 return $ PRecord rsyn fc tyn ty cn cty
  where
    getRecNames syn (PPi _ n _ sc) = [expandNS syn n, expandNS syn (mkSet n)]
                                       ++ getRecNames syn sc
    getRecNames _ _ = []

    toFreeze (Just Frozen) = Just Hidden
    toFreeze x = x

pData :: SyntaxInfo -> IParser PDecl
pData syn = try (do acc <- pAccessibility
                    reserved "data"
                    fc <- pfc
                    tyn_in <- pfName
                    ty <- pTSig (impOK syn)
                    let tyn = expandNS syn tyn_in
                    reserved "where"
                    openBlock
                    pushIndent
                    cons <- many (do notEndBlock
                                     c <- pConstructor syn
                                     pKeepTerminator
                                     return c) -- (lchar '|')
                    popIndent
                    closeBlock 
                    accData acc tyn (map (\ (n, _, _) -> n) cons)
                    return $ PData syn fc (PDatadecl tyn ty cons))
        <|> try (do pushIndent
                    acc <- pAccessibility
                    reserved "data"
                    fc <- pfc
                    tyn_in <- pfName
                    args <- many pName
                    let tyn = expandNS syn tyn_in
                    lchar '='
                    cons <- sepBy1 (pSimpleCon syn) (lchar '|')
                    pTerminator
                    let conty = mkPApp fc (PRef fc tyn) (map (PRef fc) args)
                    let ty = bindArgs (map (const PSet) args) PSet
                    cons' <- mapM (\ (x, cargs, cfc) -> 
                                 do let cty = bindArgs cargs conty
                                    return (x, cty, cfc)) cons
                    accData acc tyn (map (\ (n, _, _) -> n) cons')
                    return $ PData syn fc (PDatadecl tyn ty cons'))
  where
    mkPApp fc t [] = t
    mkPApp fc t xs = PApp fc t (map pexp xs)

bindArgs :: [PTerm] -> PTerm -> PTerm
bindArgs xs t = foldr (PPi expl (MN 0 "t")) t xs

pConstructor :: SyntaxInfo -> IParser (Name, PTerm, FC)
pConstructor syn 
    = do cn_in <- pfName; fc <- pfc
         let cn = expandNS syn cn_in
         ty <- pTSig (impOK syn)
--          ty' <- implicit syn cn ty
         return (cn, ty, fc)
 

pSimpleCon :: SyntaxInfo -> IParser (Name, [PTerm], FC)
pSimpleCon syn 
     = do cn_in <- pfName
          let cn = expandNS syn cn_in
          fc <- pfc
          args <- many (do notEndApp
                           pSimpleExpr syn)
          return (cn, args, fc)

--------- DSL syntax overloading ---------

pDSL :: SyntaxInfo -> IParser PDecl
pDSL syn = do reserved "dsl"
              n <- pfName
              openBlock
              pushIndent
              bs <- many1 (do notEndBlock
                              b <- pOverload syn
                              pKeepTerminator
                              return b)
              popIndent; closeBlock
              let dsl = mkDSL bs (dsl_info syn)
              checkDSL dsl
              i <- getState
              setState (i { idris_dsls = addDef n dsl (idris_dsls i) })
              return (PDSL n dsl)
    where mkDSL bs dsl = let var    = lookup "variable" bs
                             first  = lookup "index_first" bs
                             next   = lookup "index_next" bs
                             leto   = lookup "let" bs
                             lambda = lookup "lambda" bs in
                             initDSL { dsl_var = var,
                                       index_first = first,
                                       index_next = next,
                                       dsl_lambda = lambda,
                                       dsl_let = leto }

checkDSL :: DSL -> IParser ()
checkDSL dsl = return ()

pOverload :: SyntaxInfo -> IParser (String, PTerm)
pOverload syn = do o <- identifier <|> do reserved "let"
                                          return "let"
                   if o `notElem` overloadable
                      then fail $ show o ++ " is not an overloading"
                      else do
                        lchar '='
                        t <- pExpr syn
                        return (o, t)
    where overloadable = ["let","lambda","index_first","index_next","variable"]

--------- Pattern match clauses ---------

pPattern :: SyntaxInfo -> IParser PDecl
pPattern syn = do fc <- pfc
                  clause <- pClause syn
                  return (PClauses fc [] (MN 2 "_") [clause]) -- collect together later

pCAF :: SyntaxInfo -> IParser PDecl
pCAF syn = do reserved "let"
              n_in <- pfName; let n = expandNS syn n_in
              lchar '='
              t <- pExpr syn
              pTerminator
              fc <- pfc
              return (PCAF fc n t)

pArgExpr syn = let syn' = syn { inPattern = True } in
                   try (pHSimpleExpr syn') <|> pSimpleExtExpr syn'

pRHS :: SyntaxInfo -> Name -> IParser PTerm
pRHS syn n = do lchar '='; pExpr syn
         <|> do symbol "?="; rhs <- pExpr syn;
                return (addLet rhs)
         <|> do reserved "impossible"; return PImpossible
  where mkN (UN x)   = UN (x++"_lemma_1")
        mkN (NS x n) = NS (mkN x) n
        n' = mkN n

        addLet (PLet n ty val rhs) = PLet n ty val (addLet rhs)
        addLet (PCase fc t cs) = PCase fc t (map addLetC cs)
          where addLetC (l, r) = (l, addLet r)
        addLet rhs = (PLet (UN "value") Placeholder rhs (PMetavar n')) 

pClause :: SyntaxInfo -> IParser PClause
pClause syn
         = try (do pushIndent
                   n_in <- pfName; let n = expandNS syn n_in
                   cargs <- many (pConstraintArg syn)
                   iargs <- many (pImplicitArg syn)
                   fc <- pfc
                   args <- many (pArgExpr syn)
                   wargs <- many (pWExpr syn)
                   rhs <- pRHS syn n
                   ist <- getState
                   let ctxt = tt_ctxt ist
                   let wsyn = syn { syn_namespace = [] }
                   (wheres, nmap) <- choice [do x <- pWhereblock n wsyn
                                                popIndent
                                                return x, 
                                             do pTerminator
                                                return ([], [])]
                   let capp = PApp fc (PRef fc n) 
                                (iargs ++ cargs ++ map pexp args)
                   ist <- getState
                   setState (ist { lastParse = Just n })
                   return $ PClause fc n capp wargs rhs wheres)
       <|> try (do pushIndent
                   wargs <- many1 (pWExpr syn)
                   ist <- getState
                   n <- case lastParse ist of
                             Just t -> return t
                             Nothing -> fail "Invalid clause"
                   fc <- pfc
                   rhs <- pRHS syn n
                   let ctxt = tt_ctxt ist
                   let wsyn = syn { syn_namespace = [] }
                   (wheres, nmap) <- choice [do x <- pWhereblock n wsyn
                                                popIndent
                                                return x, 
                                             do pTerminator
                                                return ([], [])]
                   return $ PClauseR fc wargs rhs wheres)

       <|> try (do pushIndent
                   n_in <- pfName; let n = expandNS syn n_in
                   cargs <- many (pConstraintArg syn)
                   iargs <- many (pImplicitArg syn)
                   fc <- pfc
                   args <- many (pArgExpr syn)
                   wargs <- many (pWExpr syn)
                   let capp = PApp fc (PRef fc n) 
                                (iargs ++ cargs ++ map pexp args)
                   ist <- getState
                   setState (ist { lastParse = Just n })
                   reserved "with"
                   wval <- pSimpleExpr syn
                   openBlock
                   ds <- many1 $ pFunDecl syn
                   let withs = map (fillLHSD n capp wargs) $ concat ds
                   closeBlock
                   popIndent
                   return $ PWith fc n capp wargs wval withs)

       <|> try (do wargs <- many1 (pWExpr syn)
                   fc <- pfc
                   reserved "with"
                   wval <- pSimpleExpr syn
                   openBlock
                   ds <- many1 $ pFunDecl syn
                   let withs = concat ds
                   closeBlock
                   return $ PWithR fc wargs wval withs)

       <|> do pushIndent
              l <- pArgExpr syn
              op <- operator
              let n = expandNS syn (UN op)
              r <- pArgExpr syn
              fc <- pfc
              wargs <- many (pWExpr syn)
              rhs <- pRHS syn n
              let wsyn = syn { syn_namespace = [] }
              (wheres, nmap) <- choice [do x <- pWhereblock n wsyn
                                           popIndent
                                           return x, 
                                        do pTerminator
                                           return ([], [])]
              ist <- getState
              let capp = PApp fc (PRef fc n) [pexp l, pexp r]
              setState (ist { lastParse = Just n })
              return $ PClause fc n capp wargs rhs wheres

       <|> do l <- pArgExpr syn
              op <- operator
              let n = expandNS syn (UN op)
              r <- pArgExpr syn
              fc <- pfc
              wargs <- many (pWExpr syn)
              reserved "with"
              wval <- pSimpleExpr syn
              openBlock 
              ds <- many1 $ pFunDecl syn
              closeBlock
              ist <- getState
              let capp = PApp fc (PRef fc n) [pexp l, pexp r]
              let withs = map (fillLHSD n capp wargs) $ concat ds
              setState (ist { lastParse = Just n })
              return $ PWith fc n capp wargs wval withs
  where
    fillLHS n capp owargs (PClauseR fc wargs v ws) 
       = PClause fc n capp (owargs ++ wargs) v ws
    fillLHS n capp owargs (PWithR fc wargs v ws) 
       = PWith fc n capp (owargs ++ wargs) v 
            (map (fillLHSD n capp (owargs ++ wargs)) ws)
    fillLHS _ _ _ c = c

    fillLHSD n c a (PClauses fc o fn cs) = PClauses fc o fn (map (fillLHS n c a) cs)
    fillLHSD n c a x = x

pWExpr :: SyntaxInfo -> IParser PTerm
pWExpr syn = do lchar '|'
                pExpr' syn

pWhereblock :: Name -> SyntaxInfo -> IParser ([PDecl], [(Name, Name)])
pWhereblock n syn 
    = do reserved "where"; openBlock
         ds <- many1 $ pFunDecl syn
         let dns = concatMap (concatMap declared) ds
         closeBlock
         return (concat ds, map (\x -> (x, decoration syn x)) dns)

pDirective :: IParser [PDecl]
pDirective = try (do lchar '%'; reserved "lib"; lib <- strlit;
                     return [PDirective (do addLib lib
                                            addIBC (IBCLib lib))])
         <|> try (do lchar '%'; reserved "link"; obj <- strlit;
                     return [PDirective (do datadir <- liftIO getDataDir
                                            o <- liftIO $ findInPath [".", datadir] obj
                                            addIBC (IBCObj o)
                                            addObjectFile o)])
         <|> try (do lchar '%'; reserved "include"; hdr <- strlit;
                     return [PDirective (do addHdr hdr
                                            addIBC (IBCHeader hdr))])
         <|> try (do lchar '%'; reserved "hide"; n <- iName []
                     return [PDirective (do setAccessibility n Hidden
                                            addIBC (IBCAccess n Hidden))])
         <|> try (do lchar '%'; reserved "freeze"; n <- iName []
                     return [PDirective (do setAccessibility n Frozen
                                            addIBC (IBCAccess n Frozen))])
         <|> try (do lchar '%'; reserved "access"; acc <- pAccessibility'
                     return [PDirective (do i <- getIState
                                            putIState (i { default_access = acc }))])
         <|> try (do lchar '%'; reserved "logging"; i <- natural;
                     return [PDirective (setLogLevel (fromInteger i))])

pTactic :: SyntaxInfo -> IParser PTactic
pTactic syn = do reserved "intro"; ns <- sepBy pName (lchar ',')
                 return $ Intro ns
          <|> do reserved "intros"; return Intros
          <|> try (do reserved "refine"; n <- pName
                      imps <- many1 imp
                      return $ Refine n imps)
          <|> do reserved "refine"; n <- pName
                 i <- getState
                 return $ Refine n []
          <|> do reserved "rewrite"; t <- pExpr syn;
                 i <- getState
                 return $ Rewrite (desugar syn i t)
          <|> do reserved "let"; n <- pName; lchar '=';
                 t <- pExpr syn;
                 i <- getState
                 return $ LetTac n (desugar syn i t)
          <|> do reserved "focus"; n <- pName
                 return $ Focus n
          <|> do reserved "exact"; t <- pExpr syn;
                 i <- getState
                 return $ Exact (desugar syn i t)
          <|> do reserved "try"; t <- pTactic syn;
                 lchar '|';
                 t1 <- pTactic syn
                 return $ Try t t1
          <|> do lchar '{'
                 t <- pTactic syn;
                 lchar ';';
                 t1 <- pTactic syn;
                 lchar '}'
                 return $ TSeq t t1
          <|> do reserved "compute"; return Compute
          <|> do reserved "trivial"; return Trivial
          <|> do reserved "solve"; return Solve
          <|> do reserved "attack"; return Attack
          <|> do reserved "state"; return ProofState
          <|> do reserved "term"; return ProofTerm
          <|> do reserved "undo"; return Undo
          <|> do reserved "qed"; return Qed
          <|> do reserved "abandon"; return Abandon
          <|> do lchar ':'; reserved "q"; return Abandon
  where
    imp = do lchar '?'; return False
      <|> do lchar '_'; return True


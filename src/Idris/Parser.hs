module Idris.Parser where

import Idris.AbsSyntax
import Idris.Imports
import Idris.Error
import Idris.ElabDecls
import Idris.ElabTerm
import Paths_idris

import Core.CoreParser
import Core.TT
import Core.Evaluate

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as PTok

import Data.List
import Control.Monad.State
import Debug.Trace
import Data.Maybe
import System.FilePath

type TokenParser a = PTok.TokenParser a

type IParser = GenParser Char IState

lexer :: TokenParser IState
lexer  = PTok.makeTokenParser idrisDef

whiteSpace= PTok.whiteSpace lexer
lexeme    = PTok.lexeme lexer
symbol    = PTok.symbol lexer
natural   = PTok.natural lexer
parens    = PTok.parens lexer
semi      = PTok.semi lexer
comma     = PTok.comma lexer
identifier= PTok.identifier lexer
reserved  = PTok.reserved lexer
operator  = PTok.operator lexer
reservedOp= PTok.reservedOp lexer
integer   = PTok.integer lexer
float     = PTok.float lexer
strlit    = PTok.stringLiteral lexer
chlit     = PTok.charLiteral lexer
lchar = lexeme.char

-- Loading modules

loadModule :: FilePath -> Idris String
loadModule f 
   = idrisCatch (do datadir <- lift $ getDataDir
                    fp <- lift $ findImport [".", datadir] f
                    i <- getIState
                    if (f `elem` imported i)
                       then iLOG $ "Already read " ++ f
                       else do putIState (i { imported = f : imported i })
                               case fp of
                                   IDR fn -> loadSource fn
                                   IBC fn -> error "Not implemented"
                    let (dir, fh) = splitFileName f
                    return (dropExtension fh))
                (\e -> do let msg = report e
                          setErrLine (getErrLine msg)
                          iputStrLn msg
                          return "")

loadSource :: FilePath -> Idris () 
loadSource f = do iLOG ("Reading " ++ f)
                  file <- lift $ readFile f
                  (modules, rest, pos) <- parseImports f file
                  mapM_ loadModule modules
                  ds <- parseProg defaultSyntax f rest pos
                  logLvl 3 (dumpDecls ds)
                  i <- getIState
                  logLvl 10 (show (toAlist (idris_implicits i)))
                  logLvl 3 (show (idris_infixes i))
                  -- Now add all the declarations to the context
                  mapM_ (elabDecl toplevel) ds
                  iLOG ("Finished " ++ f)
                  return ()

parseExpr i = runParser (pFullExpr defaultSyntax) i "(input)"
parseTac i = runParser (do t <- pTactic defaultSyntax
                           eof
                           return t) i "(proof)"

parseImports :: FilePath -> String -> Idris ([String], String, SourcePos)
parseImports fname input 
    = do i <- get
         case (runParser (do ps <- many pImport
                             rest <- getInput
                             pos <- getPosition
                             return ((ps, rest, pos), i)) i fname input) of
            Left err -> fail (ishow err)
            Right (x, i) -> do put i
                               return x
  where ishow err = let ln = sourceLine (errorPos err) in
                        fname ++ ":" ++ show ln ++ ":parse error" 
--                           show (map messageString (errorMessages err))


pfc :: IParser FC
pfc = do s <- getPosition
         let (dir, file) = splitFileName (sourceName s)
         let f = case dir of
                    "./" -> file
                    _ -> sourceName s
         return $ FC f (sourceLine s)

pImport :: IParser String
pImport = do reserved "import"
             f <- identifier
             lchar ';'
             return f

parseProg :: SyntaxInfo -> FilePath -> String -> SourcePos -> Idris [PDecl]
parseProg syn fname input pos
    = do i <- get
         case (runParser (do setPosition pos
                             whiteSpace
                             ps <- many1 (pDecl syn)
                             eof
                             i' <- getState
                             return (concat ps, i')) i fname input) of
            Left err -> fail (ishow err)
            Right (x, i) -> do put i
                               return (collect x)
  where ishow err = let ln = sourceLine (errorPos err) in
                        fname ++ ":" ++ show ln ++ ":parse error"
--                           show (map messageString (errorMessages err))

-- Collect PClauses with the same function name

collect :: [PDecl] -> [PDecl]
collect (c@(PClauses _ o _ _) : ds) 
    = clauses (cname c) [] (c : ds)
  where clauses n acc (PClauses fc _ _ [PClause n' l ws r w] : ds)
           | n == n' = clauses n (PClause n' l ws r (collect w) : acc) ds
        clauses n acc (PClauses fc _ _ [PWith   n' l ws r w] : ds)
           | n == n' = clauses n (PWith n' l ws r (collect w) : acc) ds
        clauses n acc xs = PClauses (getfc c) o n (reverse acc) : collect xs

        cname (PClauses fc _ _ [PClause n _ _ _ _]) = n
        cname (PClauses fc _ _ [PWith   n _ _ _ _]) = n
        getfc (PClauses fc _ _ _) = fc

collect (PParams f ns ps : ds) = PParams f ns (collect ps) : collect ds
collect (PNamespace ns ps : ds) = PNamespace ns (collect ps) : collect ds
collect (PClass f s cs n ps ds : ds') = PClass f s cs n ps (collect ds) : collect ds'
collect (PInstance f s cs n ps t ds : ds') 
    = PInstance f s cs n ps t (collect ds) : collect ds'
collect (d : ds) = d : collect ds
collect [] = []

pFullExpr :: SyntaxInfo -> IParser PTerm
pFullExpr syn 
          = do x <- pExpr syn; eof;
               i <- getState
               return $ desugar syn i x

pDecl :: SyntaxInfo -> IParser [PDecl]
pDecl syn
      = do d <- pDecl' syn
           i <- getState
           let d' = fmap (desugar syn i) d
           return [d']
    <|> pUsing syn
    <|> pParams syn
    <|> pNamespace syn
    <|> pClass syn
    <|> pInstance syn
    <|> pDirective
    <|> try (do reserved "import"
                fp <- identifier
                lchar ';'
                fail "imports must be at the top of file") 

pFunDecl :: SyntaxInfo -> IParser [PDecl]
pFunDecl syn
      = try (do d <- pFunDecl' syn
                i <- getState
                let d' = fmap (desugar syn i) d
                return [d'])

--------- Top Level Declarations ---------

pDecl' :: SyntaxInfo -> IParser PDecl
pDecl' syn
       = try pFixity
     <|> pFunDecl' syn
     <|> try (pData syn)
     <|> try (pSyntaxDecl syn)

pSyntaxDecl :: SyntaxInfo -> IParser PDecl
pSyntaxDecl syn
    = do s <- pSyntaxRule syn
         i <- getState
         let rs = syntax_rules i
         let ns = syntax_keywords i
         let ks = map show (names s)
         setState (i { syntax_rules = s : rs,
                       syntax_keywords = ks ++ ns })
         fc <- pfc
         return (PSyntax fc s)
  where
    names (Rule syms _ _) = mapMaybe ename syms
    ename (Keyword n) = Just n
    ename _ = Nothing

pSyntaxRule :: SyntaxInfo -> IParser Syntax
pSyntaxRule syn 
    = do sty <- option AnySyntax (do reserved "term"; return TermSyntax
                                  <|> do reserved "pattern"; return PatternSyntax)
         reserved "syntax"
         syms <- many1 pSynSym
         when (all expr syms) $ fail "No keywords in syntax rule"
         let ns = mapMaybe name syms
         when (length ns /= length (nub ns)) 
            $ fail "Repeated variable in syntax rule"
         lchar '='
         tm <- pExpr syn
         lchar ';'
         return (Rule syms tm sty)
  where
    expr (Expr _) = True
    expr _ = False
    name (Expr n) = Just n
    name _ = Nothing

pSynSym :: IParser SSymbol
pSynSym = try (do lchar '['; n <- pName; lchar ']'
                  return (Expr n))
      <|> do n <- iName []
             return (Keyword n)
      <|> do sym <- strlit
             return (Symbol sym)

pFunDecl' :: SyntaxInfo -> IParser PDecl
pFunDecl' syn = try (do n_in <- pfName
                        let n = expandNS syn n_in
                        ty <- pTSig syn
                        fc <- pfc
                        lchar ';'
--                         ty' <- implicit syn n ty
                        return (PTy syn fc n ty))
            <|> try (pPattern syn)

pUsing :: SyntaxInfo -> IParser [PDecl]
pUsing syn = 
    do reserved "using"; 
       lchar '('
       ns <- tyDeclList syn
       lchar ')'
       lchar '{'
       let uvars = using syn
       ds <- many1 (pDecl (syn { using = uvars ++ ns }))
       lchar '}'
       return (concat ds)

pParams :: SyntaxInfo -> IParser [PDecl]
pParams syn = 
    do reserved "params"; 
       lchar '('
       ns <- tyDeclList syn
       lchar ')'
       lchar '{'
       let pvars = syn_params syn
       ds <- many1 (pDecl syn { syn_params = pvars ++ ns })
       lchar '}'
       fc <- pfc
       return [PParams fc ns (concat ds)]

pNamespace :: SyntaxInfo -> IParser [PDecl]
pNamespace syn =
    do reserved "namespace";
       n <- identifier
       lchar '{'
       ds <- many1 (pDecl syn { syn_namespace = n : syn_namespace syn })
       lchar '}'
       return [PNamespace n (concat ds)] 

expandNS :: SyntaxInfo -> Name -> Name
expandNS syn n = case syn_namespace syn of
                        [] -> n
                        xs -> NS n xs

--------- Fixity ---------

pFixity :: IParser PDecl
pFixity = do f <- fixity; i <- natural; ops <- sepBy1 operator (lchar ',')
             lchar ';'
             let prec = fromInteger i
             istate <- getState
             let fs = map (Fix (f prec)) ops
             setState (istate { 
                idris_infixes = sort (fs ++ idris_infixes istate) })
             fc <- pfc
             return (PFix fc (f prec) ops)

fixity :: IParser (Int -> Fixity) 
fixity = try (do reserved "infixl"; return Infixl)
     <|> try (do reserved "infixr"; return Infixr)
     <|> try (do reserved "infix";  return InfixN)
     <|> try (do reserved "prefix"; return PrefixN)

--------- Tyoe classes ---------

pClass :: SyntaxInfo -> IParser [PDecl]
pClass syn = do reserved "class"
                fc <- pfc
                cons <- pConstList syn
                n_in <- pName; let n = expandNS syn n_in
                cs <- many1 carg
                reserved "where"; lchar '{'
                ds <- many1 $ pFunDecl syn;
                lchar '}'
                return [PClass syn fc cons n cs (concat ds)]
  where
    carg = do lchar '('; i <- pName; lchar ':'; ty <- pExpr syn; lchar ')'
              return (i, ty)
       <|> do i <- pName;
              return (i, PSet)

pInstance :: SyntaxInfo -> IParser [PDecl]
pInstance syn = do reserved "instance"
                   fc <- pfc
                   cs <- pConstList syn
                   cn <- pName
                   args <- many1 (pSimpleExpr syn)
                   let sc = PApp fc (PRef fc cn) (map pexp args)
                   let t = bindList (PPi constraint) (map (\x -> (MN 0 "c", x)) cs) sc
                   reserved "where"; lchar '{'
                   ds <- many1 $ pFunDecl syn;
                   lchar '}'
                   return [PInstance syn fc cs cn args t (concat ds)]

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
    simple (Rule [Keyword _] _ _) = True
    simple (Rule [Symbol _]  _ _) = True
    simple (Rule (_:xs) _ _) = case (last xs) of
        Keyword _ -> True
        Symbol _  -> True
        _ -> False
    simple _ = False

pNoExtExpr syn =
         try (pApp syn) 
     <|> pSimpleExpr syn
     <|> pLambda syn
     <|> pLet syn
     <|> pPi syn 
     <|> pDoBlock syn
    
pExtensions :: SyntaxInfo -> [Syntax] -> IParser PTerm
pExtensions syn rules = choice (map (\x -> try (pExt syn x)) (filter valid rules))
  where
    valid (Rule _ _ AnySyntax) = True
    valid (Rule _ _ PatternSyntax) = inPattern syn
    valid (Rule _ _ TermSyntax) = not (inPattern syn)


pExt :: SyntaxInfo -> Syntax -> IParser PTerm
pExt syn (Rule (s:ssym) ptm _)
    = do s1 <- pSymbol pSimpleExpr s 
         smap <- mapM (pSymbol pExpr') ssym
         let ns = mapMaybe id (s1:smap)
         return (update ns ptm) -- updated with smap
  where
    pSymbol p (Keyword n) = do reserved (show n); return Nothing
    pSymbol p (Expr n)    = do tm <- p syn
                               return $ Just (n, tm)
    pSymbol p (Symbol s)  = do symbol s
                               return Nothing
    dropn n [] = []
    dropn n ((x,t) : xs) | n == x = xs
                         | otherwise = (x,t):dropn n xs

    update ns (PRef fc n) = case lookup n ns of
                              Just t -> t
                              _ -> PRef fc n
    update ns (PLam n ty sc) = PLam n (update ns ty) (update (dropn n ns) sc)
    update ns (PPi p n ty sc) = PPi p n (update ns ty) (update (dropn n ns) sc) 
    update ns (PLet n ty val sc) = PLet n (update ns ty) (update ns val)
                                          (update (dropn n ns) sc)
    update ns (PApp fc t args) = PApp fc (update ns t) (map (fmap (update ns)) args)
    update ns (PPair fc l r) = PPair fc (update ns l) (update ns r)
    update ns (PDPair fc l t r) = PDPair fc (update ns l) (update ns t) (update ns r)
    update ns (PAlternative as) = PAlternative (map (update ns) as)
    update ns (PHidden t) = PHidden (update ns t)
    update ns (PDoBlock ds) = PDoBlock $ upd ns ds
      where upd ns (DoExp fc t : ds) = DoExp fc (update ns t) : upd ns ds
            upd ns (DoBind fc n t : ds) = DoBind fc n (update ns t) : upd (dropn n ns) ds
            upd ns (DoLet fc n t : ds) = DoLet fc n (update ns t) : upd (dropn n ns) ds
    update ns t = t

pName = do i <- getState
           iName (syntax_keywords i)
    <|> do reserved "instance"
           i <- getState
           UN n <- iName (syntax_keywords i)
           return (UN ('@':n))
    

pfName = try pName
     <|> do lchar '('; o <- operator; lchar ')'; return (UN o)

pSimpleExpr syn = 
        try (do symbol "!["; t <- pTerm; lchar ']' 
                return $ PQuote t)
        <|> do lchar '?'; x <- pName; return (PMetavar x)
        <|> do reserved "refl"; fc <- pfc; return (PRefl fc)
--         <|> do reserved "return"; fc <- pfc; return (PReturn fc)
        <|> do reserved "proof"; lchar '{';
               ts <- endBy (pTactic syn) (lchar ';')
               lchar '}'
               return (PProof ts)
        <|> do reserved "tactics"; lchar '{';
               ts <- endBy (pTactic syn) (lchar ';')
               lchar '}'
               return (PTactics ts)
        <|> try (do x <- pfName; fc <- pfc; return (PRef fc x))
        <|> try (pPair syn)
        <|> try (pList syn)
        <|> try (pAlt syn)
        <|> try (do lchar '('; e <- pExpr syn; lchar ')'; return e)
        <|> try (do c <- pConstant; fc <- pfc
                    return (modifyConst syn fc (PConstant c)))
        <|> do reserved "Set"; return PSet
        <|> try (do symbol "()"; fc <- pfc; return (PTrue fc))
        <|> try (do symbol "_|_"; fc <- pfc; return (PFalse fc))
        <|> do lchar '_'; return Placeholder
        <|> pSimpleExtExpr syn

modifyConst :: SyntaxInfo -> FC -> PTerm -> PTerm
modifyConst syn fc (PConstant (I x)) 
    | not (inPattern syn)
        = PApp fc (PRef fc (UN "fromInteger")) [pexp (PConstant (I x))]
modifyConst syn fc x = x

pList syn = do lchar '['; fc <- pfc
               xs <- sepBy (pExpr syn) (lchar ','); lchar ']'
               return (mkList fc xs)
  where
    mkList fc [] = PRef fc (UN "Nil")
    mkList fc (x : xs) = PApp fc (PRef fc (UN "::")) [pexp x, pexp (mkList fc xs)] 

pPair syn = try (do lchar '('; l <- pExpr syn; op <- pairOp
                    fc <- pfc
                    r <- pExpr syn; lchar ')';
                    return (op fc l r))
        <|> do lchar '('; ln <- pName; lchar ':'; lty <- pExpr syn;
               reservedOp "**";
               fc <- pfc
               r <- pExpr syn; lchar ')';
               return (PDPair fc (PRef fc ln) lty r) 
  where
    pairOp = do lchar ','; return PPair
         <|> do reservedOp "**"; return (\f x y -> PDPair f x Placeholder y)
       
pAlt syn = do symbol "(|"; 
              alts <- sepBy1 (pExpr' syn) (lchar ',')
              symbol "|)"
              return (PAlternative alts)

pHSimpleExpr syn
             = do lchar '.'
                  e <- pSimpleExpr syn
                  return $ PHidden e
           <|> pSimpleExpr syn

pApp syn = do f <- pSimpleExpr syn
              fc <- pfc
              args <- many1 (pArg syn)
              return (PApp fc f args)

pArg :: SyntaxInfo -> IParser PArg
pArg syn = try (pImplicitArg syn)
       <|> try (pConstraintArg syn)
       <|> do e <- pSimpleExpr syn
              return (pexp e)

pImplicitArg syn = do lchar '{'; n <- pName
                      fc <- pfc
                      v <- option (PRef fc n) (do lchar '='; pExpr syn)
                      lchar '}'
                      return (pimp n v)

pConstraintArg syn = do symbol "@{"; e <- pExpr syn; symbol "}"
                        return (pconst e)

pTSig syn = do lchar ':'
               cs <- pConstList syn
               sc <- pExpr syn
               return (bindList (PPi constraint) (map (\x -> (MN 0 "c", x)) cs) sc)

pLambda syn = do lchar '\\'; 
                 xt <- tyOptDeclList syn
                 symbol "=>"
                 sc <- pExpr syn
                 return (bindList PLam xt sc)

pLet syn = do reserved "let"; n <- pName; 
              ty <- option Placeholder (do lchar ':'; pExpr' syn)
              lchar '='; v <- pExpr syn
              reserved "in";  sc <- pExpr syn
              return (PLet n ty v sc)

pPi syn = 
     try (do lazy <- option False (do lchar '|'; return True)
             st <- pStatic
             lchar '('; xt <- tyDeclList syn; lchar ')'
             symbol "->"
             sc <- pExpr syn
             return (bindList (PPi (Exp lazy st)) xt sc))
 <|> try (do lazy <- option False (do lchar '|'; return True)
             st <- pStatic
             lchar '{'; xt <- tyDeclList syn; lchar '}'
             symbol "->"
             sc <- pExpr syn
             return (bindList (PPi (Imp lazy st)) xt sc))
      <|> do --lazy <- option False (do lchar '|'; return True)
             lchar '{'; reserved "static"; lchar '}'
             t <- pExpr' syn
             symbol "->"
             sc <- pExpr syn
             return (PPi (Exp False Static) (MN 42 "__pi_arg") t sc)

pConstList :: SyntaxInfo -> IParser [PTerm]
pConstList syn = try (do lchar '(' 
                         tys <- sepBy1 (pExpr' syn) (lchar ',')
                         lchar ')'
                         reservedOp "=>"
                         return tys)
             <|> try (do t <- pExpr syn
                         reservedOp "=>"
                         return [t])
             <|> return []

tyDeclList syn = try (sepBy1 (do x <- pfName; t <- pTSig syn; return (x,t))
                         (lchar ','))
             <|> do ns <- sepBy1 pName (lchar ',')
                    t <- pTSig syn
                    return (map (\x -> (x, t)) ns)

tyOptDeclList syn = sepBy1 (do x <- pfName; 
                               t <- option Placeholder (do lchar ':'
                                                           pExpr syn) 
                               return (x,t))
                           (lchar ',')

bindList b []          sc = sc
bindList b ((n, t):bs) sc = b n t (bindList b bs sc)

pDoBlock syn 
    = do reserved "do"; lchar '{'
         ds <- endBy1 (pDo syn) (lchar ';')
         lchar '}'
         return (PDoBlock ds)

pDo syn
     = do reserved "let"; i <- pName; reservedOp "="; fc <- pfc
          e <- pExpr syn
          return (DoLet fc i e)
   <|> try (do i <- pName; symbol "<-"; fc <- pfc
               e <- pExpr syn;
               return (DoBind fc i e))
   <|> try (do e <- pExpr syn; fc <- pfc
               return (DoExp fc e))

pConstant :: IParser Const
pConstant = do reserved "Integer";return BIType
        <|> do reserved "Int";    return IType
        <|> do reserved "Char";   return ChType
        <|> do reserved "Float";  return FlType
        <|> do reserved "String"; return StrType
        <|> do reserved "Ptr";    return PtrType
        <|> try (do f <- float;   return $ Fl f)
        <|> try (do i <- natural; lchar 'L'; return $ BI i)
        <|> try (do i <- natural; return $ I (fromInteger i))
        <|> try (do s <- strlit;  return $ Str s)
        <|> try (do c <- chlit;   return $ Ch c)

pStatic :: IParser Static
pStatic = do lchar '['; reserved "static"; lchar ']';
             return Static
         <|> return Dynamic

table fixes 
   = [[prefix "-" (\fc x -> PApp fc (PRef fc (UN "-")) 
        [pexp (PApp fc (PRef fc (UN "fromInteger")) [pexp (PConstant (I 0))]), pexp x])]] 
       ++ toTable (reverse fixes) ++
      [[binary "="  (\fc x y -> PEq fc x y) AssocLeft],
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

binary name f assoc = Infix (do { reservedOp name; fc <- pfc; 
                                  return (f fc) }) assoc
prefix name f = Prefix (do { reservedOp name; fc <- pfc;
                             return (f fc) })

--------- Data declarations ---------

pData :: SyntaxInfo -> IParser PDecl
pData syn = try (do reserved "data"; fc <- pfc
                    tyn_in <- pfName; ty <- pTSig syn
                    let tyn = expandNS syn tyn_in
                    reserved "where"
--                     ty' <- implicit syn tyn ty
                    cons <- sepBy (pConstructor syn) (lchar '|')
                    lchar ';'
                    return $ PData syn fc (PDatadecl tyn ty cons))
        <|> do reserved "data"; fc <- pfc
               tyn_in <- pfName; args <- many pName
               let tyn = expandNS syn tyn_in
               lchar '='
               cons <- sepBy1 (pSimpleCon syn) (lchar '|')
               lchar ';'
               let conty = mkPApp fc (PRef fc tyn) (map (PRef fc) args)
               let ty = bindArgs (map (\a -> PSet) args) PSet
--                ty' <- implicit syn tyn ty
               cons' <- mapM (\ (x, cargs, cfc) -> 
                                 do let cty = bindArgs cargs conty
--                                     cty' <- implicit syn x cty
                                    return (x, cty, cfc)) cons
               return $ PData syn fc (PDatadecl tyn ty cons')
  where
    mkPApp fc t [] = t
    mkPApp fc t xs = PApp fc t (map pexp xs)

bindArgs :: [PTerm] -> PTerm -> PTerm
bindArgs [] t = t
bindArgs (x:xs) t = PPi expl (MN 0 "t") x (bindArgs xs t)

pConstructor :: SyntaxInfo -> IParser (Name, PTerm, FC)
pConstructor syn
    = do cn_in <- pfName; fc <- pfc
         let cn = expandNS syn cn_in
         ty <- pTSig syn
--          ty' <- implicit syn cn ty
         return (cn, ty, fc)

pSimpleCon :: SyntaxInfo -> IParser (Name, [PTerm], FC)
pSimpleCon syn 
     = do cn_in <- pfName
          let cn = expandNS syn cn_in
          fc <- pfc
          args <- many (pSimpleExpr syn)
          return (cn, args, fc)

--------- Pattern match clauses ---------

pPattern :: SyntaxInfo -> IParser PDecl
pPattern syn = do clause <- pClause syn
                  fc <- pfc
                  return (PClauses fc False (MN 2 "_") [clause]) -- collect together later

pArgExpr syn = let syn' = syn { inPattern = True } in
                   try (pHSimpleExpr syn') <|> pSimpleExtExpr syn'

pRHS :: SyntaxInfo -> Name -> IParser PTerm
pRHS syn n = do lchar '='; pExpr syn
         <|> do symbol "?="; rhs <- pExpr syn;
                return (PLet (UN "value") Placeholder rhs (PMetavar n')) 
  where n' = case n of
                UN x -> UN (x++"_lemma_1")
                x -> x

pClause :: SyntaxInfo -> IParser PClause
pClause syn
         = try (do n_in <- pfName; let n = expandNS syn n_in
                   cargs <- many (pConstraintArg syn)
                   iargs <- many (pImplicitArg syn)
                   fc <- pfc
                   args <- many (pArgExpr syn)
                   wargs <- many (pWExpr syn)
                   rhs <- pRHS syn n
                   ist <- getState
                   let ctxt = tt_ctxt ist
                   let wsyn = syn { syn_namespace = [] }
                   (wheres, nmap) <- choice [pWhereblock n wsyn, 
                                             do lchar ';'
                                                return ([], [])]
                   return $ PClause n (PApp fc (PRef fc n) 
                                      (iargs ++ cargs ++ map pexp args)) wargs rhs wheres)
       <|> try (do n_in <- pfName; let n = expandNS syn n_in
                   cargs <- many (pConstraintArg syn)
                   iargs <- many (pImplicitArg syn)
                   fc <- pfc
                   args <- many (pArgExpr syn)
                   wargs <- many (pWExpr syn)
                   reserved "with"
                   wval <- pExpr syn
                   lchar '{'
                   ds <- many1 $ pFunDecl syn
                   let withs = concat ds
                   lchar '}'
                   return $ PWith n (PApp fc (PRef fc n) 
                                       (iargs ++ cargs ++ map pexp args)) wargs wval withs)

       <|> do l <- pArgExpr syn
              op <- operator
              let n = expandNS syn (UN op)
              r <- pArgExpr syn
              fc <- pfc
              wargs <- many (pWExpr syn)
              rhs <- pRHS syn n
              let wsyn = syn { syn_namespace = [] }
              (wheres, nmap) <- choice [pWhereblock n wsyn, 
                                        do lchar ';'
                                           return ([], [])]
              return $ PClause n (PApp fc (PRef fc n) [pexp l,pexp r]) 
                                 wargs rhs wheres

       <|> do l <- pArgExpr syn
              op <- operator
              let n = expandNS syn (UN op)
              r <- pArgExpr syn
              fc <- pfc
              wargs <- many (pWExpr syn)
              reserved "with"
              wval <- pExpr syn
              lchar '{'
              ds <- many1 $ pFunDecl syn
              let withs = concat ds
              lchar '}'
              return $ PWith n (PApp fc (PRef fc n) [pexp l, pexp r]) wargs wval withs

pWExpr :: SyntaxInfo -> IParser PTerm
pWExpr syn = do lchar '|'; pExpr' syn

pWhereblock :: Name -> SyntaxInfo -> IParser ([PDecl], [(Name, Name)])
pWhereblock n syn 
    = do reserved "where"; lchar '{'
         ds <- many1 $ pFunDecl syn;
         let dns = concatMap (concatMap declared) ds
         lchar '}';
         return (concat ds, map (\x -> (x, decoration syn x)) dns)

pDirective :: IParser [PDecl]
pDirective = try (do lchar '%'; reserved "lib"; lib <- strlit;
                     return [PDirective (addLib lib)])
         <|> try (do lchar '%'; reserved "link"; obj <- strlit;
                     return [PDirective (do datadir <- lift $ getDataDir
                                            o <- lift $ findInPath [".", datadir] obj
                                            addObjectFile o)])
         <|> try (do lchar '%'; reserved "include"; hdr <- strlit;
                     return [PDirective (addHdr hdr)])
         <|> do lchar '%'; reserved "logging"; i <- natural;
                return [PDirective (setLogLevel (fromInteger i))] 

pTactic :: SyntaxInfo -> IParser PTactic
pTactic syn = do reserved "intro"; ns <- sepBy pName (lchar ',')
                 return $ Intro ns
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
  where
    imp = do lchar '?'; return False
      <|> do lchar '_'; return True

desugar :: SyntaxInfo -> IState -> PTerm -> PTerm
desugar syn i t = let t' = expandDo (dsl_info syn) t in
                      t' -- addImpl i t'

expandDo :: DSL -> PTerm -> PTerm
expandDo dsl (PLam n ty tm) = PLam n (expandDo dsl ty) (expandDo dsl tm)
expandDo dsl (PPi p n ty tm) = PPi p n (expandDo dsl ty) (expandDo dsl tm)
expandDo dsl (PApp fc t args) = PApp fc (expandDo dsl t)
                                        (map (fmap (expandDo dsl)) args)
expandDo dsl (PPair fc l r) = PPair fc (expandDo dsl l) (expandDo dsl r)
expandDo dsl (PDPair fc l t r) = PDPair fc (expandDo dsl l) (expandDo dsl t) 
                                           (expandDo dsl r)
expandDo dsl (PAlternative as) = PAlternative (map (expandDo dsl) as)
expandDo dsl (PHidden t) = PHidden (expandDo dsl t)
expandDo dsl (PReturn fc) = PRef fc (dsl_return dsl)
expandDo dsl (PDoBlock ds) = expandDo dsl $ block (dsl_bind dsl) ds 
  where
    block b [DoExp fc tm] = tm 
    block b [a] = PElabError "Last statement in do block must be an expression"
    block b (DoBind fc n tm : rest)
        = PApp fc (PRef fc b) [pexp tm, pexp (PLam n Placeholder (block b rest))]
    block b (DoExp fc tm : rest)
        = PApp fc (PRef fc b) 
            [pexp tm, 
             pexp (PLam (MN 0 "bindx") Placeholder (block b rest))]
expandDo dsl t = t




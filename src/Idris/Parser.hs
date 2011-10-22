module Idris.Parser where

import Idris.AbsSyntax
import Idris.Imports
import Paths_miniidris
import Idris.ElabDecls

import Core.CoreParser
import Core.TT

import Text.ParserCombinators.Parsec
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

loadModule :: FilePath -> Idris ()
loadModule f = do datadir <- lift $ getDataDir
                  fp <- lift $ findImport [".", datadir] f
                  i <- getIState
                  if (f `elem` imported i)
                     then iLOG $ "Already read " ++ f
                     else do putIState (i { imported = f : imported i })
                             case fp of
                                 IDR fn -> loadSource fn
                                 IBC fn -> error "Not implemented"

loadSource :: FilePath -> Idris () 
loadSource f = do iLOG ("Reading " ++ f)
                  file <- lift $ readFile f
                  (modules, rest, pos) <- parseImports f file
                  mapM_ loadModule modules
                  ds <- parseProg defaultSyntax f rest pos
                  logLvl 3 (dumpDecls ds)
                  i <- getIState
                  logLvl 3 (show (idris_infixes i))
                  -- Now add all the declarations to the context
                  mapM_ (elabDecl toplevel) ds
                  iLOG ("Finished " ++ f)
                  return ()

parseExpr i = runParser (pFullExpr defaultSyntax) i "(input)"

parseImports :: FilePath -> String -> Idris ([String], String, SourcePos)
parseImports fname input 
    = do i <- get
         case (runParser (do ps <- many pImport
                             rest <- getInput
                             pos <- getPosition
                             return ((ps, rest, pos), i)) i fname input) of
            Left err -> fail (show err)
            Right (x, i) -> do put i
                               return x

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
            Left err -> fail (show err)
            Right (x, i) -> do put i
                               return (collect x)

-- Collect PClauses with the same function name
collect :: [PDecl] -> [PDecl]
collect (c@(PClauses fc _ [PClause n l r w]) : ds) = clauses n [] (c:ds)
  where clauses n acc (PClauses fc _ [PClause n' l r w] : ds)
           | n == n' = clauses n (PClause n' l r (collect w) : acc) ds
        clauses n acc xs = PClauses fc n (reverse acc) : collect xs
collect (PParams f ns ps : ds) = PParams f ns (collect ps) : (collect ds)
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
    <|> try (pUsing syn)
    <|> try (pParams syn)
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
         setState (i { syntax_rules = s : syntax_rules i })
         fc <- pfc
         return (PSyntax fc s)

pSyntaxRule :: SyntaxInfo -> IParser Syntax
pSyntaxRule syn 
    = do reserved "syntax"
         syms <- many1 pSynSym
         when (all expr syms) $ fail "No keywords in syntax rule"
         let ns = mapMaybe name syms
         when (length ns /= length (nub ns)) 
            $ fail "Repeated variable in syntax rule"
         lchar '='
         tm <- pExpr syn
         lchar ';'
         return (Rule syms tm)
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
pFunDecl' syn = try (do fc <- pfc
                        n <- pfName; ty <- pTSig syn
                        lchar ';'
                        ty' <- implicit syn n ty
                        return (PTy fc n ty'))
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

--------- Expressions ---------

pExpr syn = do i <- getState
               buildExpressionParser (table (idris_infixes i)) (pExpr' syn)

pExpr' :: SyntaxInfo -> IParser PTerm
pExpr' syn 
       = try (do i <- getState
                 pExtensions syn (syntax_rules i)) 
     <|> pNoExtExpr syn

pNoExtExpr syn =
         try (pApp syn) 
     <|> pSimpleExpr syn
     <|> try (pLambda syn)
     <|> try (pPi syn) 
     <|> try (pDoBlock syn)
    
pExtensions :: SyntaxInfo -> [Syntax] -> IParser PTerm
pExtensions syn rules = choice (map (\x -> try (pExt syn x)) rules)

pExt :: SyntaxInfo -> Syntax -> IParser PTerm
pExt syn (Rule (s:ssym) ptm)
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

    update ns (PRef n) = case lookup n ns of
                            Just t -> t
                            _ -> PRef n
    update ns (PLam n ty sc) = PLam n (update ns ty) (update (dropn n ns) sc)
    update ns (PPi p n ty sc) = PPi p n (update ns ty) (update (dropn n ns) sc) 
    update ns (PLet n ty val sc) = PLet n (update ns ty) (update ns val)
                                          (update (dropn n ns) sc)
    update ns (PApp t args) = PApp (update ns t) (map (fmap (update ns)) args)
    update ns (PPair l r) = PPair (update ns l) (update ns r)
    update ns (PHidden t) = PHidden (update ns t)
    update ns (PDoBlock ds) = PDoBlock $ upd ns ds
      where upd ns (DoExp t : ds) = DoExp (update ns t) : upd ns ds
            upd ns (DoBind n t : ds) = DoBind n (update ns t) : upd (dropn n ns) ds
            upd ns (DoLet n t : ds) = DoLet n (update ns t) : upd (dropn n ns) ds
    update ns t = t

pName = do i <- getState
           iName (map show (names (syntax_rules i)))
  where
    names rs = concatMap namesR rs
    namesR (Rule syms _) = mapMaybe ename syms
    ename (Keyword n) = Just n
    ename _ = Nothing

pfName = try pName
     <|> do lchar '('; o <- operator; lchar ')'; return (UN [o])

pSimpleExpr syn = 
        try (do symbol "!["; t <- pTerm; lchar ']' 
                return $ PQuote t)
        <|> try (do lchar '?'; x <- pName; return (PMetavar x))
        <|> try (do reserved "return"; return PReturn)
        <|> try (do x <- pfName; return (PRef x))
        <|> try (do lchar '('; l <- pExpr syn; lchar ','; r <- pExpr syn; lchar ')';
                    return (PPair l r))
        <|> try (do lchar '('; e <- pExpr syn; lchar ')'; return e)
        <|> try (do c <- pConstant; return (PConstant c))
        <|> try (do reserved "Set"; return PSet)
        <|> try (do symbol "()"; return PTrue)
        <|> try (do symbol "_|_"; return PFalse)
        <|> try (do lchar '_'; return Placeholder)

pHSimpleExpr syn
             = try (pSimpleExpr syn)
           <|> do lchar '.'
                  e <- pSimpleExpr syn
                  return $ PHidden e

pApp syn = do f <- pSimpleExpr syn
              args <- many1 (pArg syn)
              return (PApp f args)

pArg :: SyntaxInfo -> IParser PArg
pArg syn = pImplicitArg syn
       <|> do e <- pSimpleExpr syn
              return (PExp e)

pImplicitArg syn = do lchar '{'; n <- pName
                      v <- option (PRef n) (do lchar '='; pExpr syn)
                      lchar '}'
                      return (PImp n v)

pTSig syn = do lchar ':'
               pExpr syn

pLambda syn = do lchar '\\'; 
                 xt <- tyOptDeclList syn
                 symbol "=>"
                 sc <- pExpr syn
                 return (bindList PLam xt sc)

pPi syn = do lchar '('; xt <- tyDeclList syn; lchar ')'
             symbol "->"
             sc <- pExpr syn
             return (bindList (PPi Exp) xt sc)
      <|> do lchar '{'; xt <- tyDeclList syn; lchar '}'
             symbol "->"
             sc <- pExpr syn
             return (bindList (PPi Imp) xt sc)

tyDeclList syn = sepBy1 (do x <- pfName; t <- pTSig syn; return (x,t))
                    (lchar ',')

tyOptDeclList syn = sepBy1 (do x <- pfName; t <- option Placeholder (pTSig syn) 
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
     = try (do i <- pName; symbol "<-"; e <- pExpr syn;
               return (DoBind i e))
   <|> try (do reserved "let"; i <- pName; reservedOp "="; e <- pExpr syn
               return (DoLet i e))
   <|> try (do e <- pExpr syn; return (DoExp e))

pConstant :: IParser Const
pConstant = do reserved "Int";    return IType
        <|> do reserved "Char";   return ChType
        <|> do reserved "Float";  return FlType
        <|> do reserved "String"; return StrType
        <|> do reserved "Ptr";    return PtrType
        <|> try (do f <- float;   return $ Fl f)
        <|> try (do i <- natural; return $ I (fromInteger i))
        <|> try (do s <- strlit;  return $ Str s)
        <|> try (do c <- chlit;   return $ Ch c)

table fixes 
   = [[prefix "-" (\x -> PApp (PRef (UN ["-"])) [PExp (PConstant (I 0)), PExp x])]] 
       ++ toTable (reverse fixes) ++
      [[binary "="  (\x y -> PApp (PRef (UN ["="])) [PExp x,PExp y]) AssocLeft],
       [binary "->" (PPi Exp (MN 0 "X")) AssocRight]]

toTable fs = map (map toBin) 
                 (groupBy (\ (Fix x _) (Fix y _) -> prec x == prec y) fs)
   where toBin (Fix (PrefixN _) op) = prefix op 
                                       (\x -> PApp (PRef (UN [op])) [PExp x])
         toBin (Fix f op) = binary op 
                               (\x y -> PApp (PRef (UN [op])) [PExp x,PExp y]) (assoc f)
         assoc (Infixl _) = AssocLeft
         assoc (Infixr _) = AssocRight
         assoc (InfixN _) = AssocNone

binary name f assoc = Infix (do { reservedOp name; return f }) assoc
prefix name f = Prefix (do { reservedOp name; return f })

--------- Data declarations ---------

pData :: SyntaxInfo -> IParser PDecl
pData syn = try (do fc <- pfc
                    reserved "data"; tyn <- pfName; ty <- pTSig syn
                    reserved "where"
                    ty' <- implicit syn tyn ty
                    cons <- sepBy (pConstructor syn) (lchar '|')
                    lchar ';'
                    return $ PData fc (PDatadecl tyn ty' cons))
        <|> do fc <- pfc
               reserved "data"; tyn <- pfName; args <- many pName
               lchar '='
               cons <- sepBy1 (pSimpleCon syn) (lchar '|')
               lchar ';'
               let conty = mkPApp (PRef tyn) (map PRef args)
               let ty = bindArgs (map (\a -> PSet) args) PSet
               ty' <- implicit syn tyn ty
               cons' <- mapM (\ (x, cargs, cfc) -> 
                                 do let cty = bindArgs cargs conty
                                    cty' <- implicit syn x cty
                                    return (x, cty', cfc)) cons
               return $ PData fc (PDatadecl tyn ty' cons')

mkPApp t [] = t
mkPApp t xs = PApp t (map PExp xs)

bindArgs :: [PTerm] -> PTerm -> PTerm
bindArgs [] t = t
bindArgs (x:xs) t = PPi Exp (MN 0 "t") x (bindArgs xs t)

pConstructor :: SyntaxInfo -> IParser (Name, PTerm, FC)
pConstructor syn
    = do fc <- pfc
         cn <- pfName; ty <- pTSig syn
         ty' <- implicit syn cn ty
         return (cn, ty', fc)

pSimpleCon :: SyntaxInfo -> IParser (Name, [PTerm], FC)
pSimpleCon syn 
     = do fc <- pfc
          cn <- pfName
          args <- many (pSimpleExpr syn)
          return (cn, args, fc)

--------- Pattern match clauses ---------

pPattern :: SyntaxInfo -> IParser PDecl
pPattern syn = do fc <- pfc
                  clause <- pClause syn
                  return (PClauses fc (MN 2 "_") [clause]) -- collect together later

pClause :: SyntaxInfo -> IParser PClause
pClause syn
        = try (do n <- pfName
                  iargs <- many (pImplicitArg syn)
                  args <- many (pHSimpleExpr syn)
                  lchar '='
                  rhs <- pExpr syn
                  wheres <- choice [pWhereblock syn, do lchar ';'; return []]
                  return $ PClause n (PApp (PRef n) (iargs ++ map PExp args)) rhs wheres)
       <|> do l <- pSimpleExpr syn
              op <- operator
              let n = UN [op]
              r <- pSimpleExpr syn
              lchar '='
              rhs <- pExpr syn
              wheres <- choice [pWhereblock syn, do lchar ';'; return []]
              return $ PClause n (PApp (PRef n) [PExp l,PExp r]) rhs wheres

pWhereblock :: SyntaxInfo -> IParser [PDecl]
pWhereblock syn = do reserved "where"; lchar '{'
                     ds <- many1 $ pFunDecl syn;
                     lchar '}';
                     return $ concat ds

-- Dealing with implicit arguments

implicit :: SyntaxInfo -> Name -> PTerm -> IParser PTerm
implicit syn n ptm 
    = do i <- getState
         let (tm', impdata) = implicitise syn i ptm
         setState (i { idris_implicits = addDef n impdata (idris_implicits i) })
         return tm'

desugar :: SyntaxInfo -> IState -> PTerm -> PTerm
desugar syn i t = let t' = expandDo (dsl_info syn) t in
                      addImpl i t'

expandDo :: DSL -> PTerm -> PTerm
expandDo dsl (PLam n ty tm) = PLam n (expandDo dsl ty) (expandDo dsl tm)
expandDo dsl (PPi p n ty tm) = PPi p n (expandDo dsl ty) (expandDo dsl tm)
expandDo dsl (PApp t args) = PApp (expandDo dsl t)
                                  (map (fmap (expandDo dsl)) args)
expandDo dsl (PPair l r) = PPair (expandDo dsl l) (expandDo dsl r)
expandDo dsl (PHidden t) = PHidden (expandDo dsl t)
expandDo dsl PReturn = PRef (dsl_return dsl)
expandDo dsl (PDoBlock ds) = expandDo dsl $ block (dsl_bind dsl) ds 
  where
    block b [DoExp tm] = tm 
    block b [a] = PElabError "Last statement in do block must be an expression"
    block b (DoBind n tm : rest)
        = PApp (PRef b) [PExp tm, PExp (PLam n Placeholder (block b rest))]
    block b (DoExp tm : rest)
        = PApp (PRef b) [PExp tm, PExp (PLam (MN 0 "bindx") Placeholder (block b rest))]
expandDo dsl t = t




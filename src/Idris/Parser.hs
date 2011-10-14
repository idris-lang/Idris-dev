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
collect (c@(PClauses _ [PClause n l r w]) : ds) = clauses n [] (c:ds)
  where clauses n acc (PClauses _ [PClause n' l r w] : ds)
           | n == n' = clauses n (PClause n' l r (collect w) : acc) ds
        clauses n acc xs = PClauses n (reverse acc) : collect xs
collect (PParams ns ps : ds) = PParams ns (collect ps) : (collect ds)
collect (d : ds) = d : collect ds
collect [] = []

pFullExpr :: SyntaxInfo -> IParser PTerm
pFullExpr syn 
          = do x <- pExpr syn; eof; 
               i <- getState
               return (addImpl i x)

pDecl :: SyntaxInfo -> IParser [PDecl]
pDecl syn
      = do d <- pDecl' syn
           i <- getState
           return [fmap (addImpl i) d]
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
                return [fmap (addImpl i) d])

--------- Top Level Declarations ---------

pDecl' :: SyntaxInfo -> IParser PDecl
pDecl' syn
       = try pFixity
     <|> pFunDecl' syn
     <|> try (pData syn)

pFunDecl' :: SyntaxInfo -> IParser PDecl
pFunDecl' syn = try (do n <- pfName; ty <- pTSig syn
                        lchar ';'
                        ty' <- implicit syn n ty
                        return (PTy n ty'))
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
       return [PParams ns (concat ds)]

--------- Fixity ---------

pFixity :: IParser PDecl
pFixity = do f <- fixity; i <- natural; ops <- sepBy1 operator (lchar ',')
             lchar ';'
             let prec = fromInteger i
             istate <- getState
             let fs = map (Fix (f prec)) ops
             setState (istate { 
                idris_infixes = sort (fs ++ idris_infixes istate) })
             return (PFix (f prec) ops)

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
       = try (pApp syn) 
     <|> pSimpleExpr syn
     <|> try (pLambda syn)
     <|> try (pPi syn) 

pfName = try iName
     <|> do lchar '('; o <- operator; lchar ')'; return (UN [o])

pSimpleExpr syn = 
        try (do symbol "!["; t <- pTerm; lchar ']' 
                return $ PQuote t)
        <|> try (do x <- pfName; return (PRef x))
        <|> try (do lchar '_'; return Placeholder)
        <|> try (do lchar '('; e <- pExpr syn; lchar ')'; return e)
        <|> try (do c <- pConstant; return (PConstant c))
        <|> try (do reserved "Set"; return PSet)

pHSimpleExpr syn
             = try (pSimpleExpr syn)
           <|> do lchar '.'
                  e <- pSimpleExpr syn
                  return $ PHidden e

pApp syn = do f <- pSimpleExpr syn
              iargs <- many (pImplicitArg syn)
              args <- many1 (pSimpleExpr syn)
              return (PApp f (iargs ++ map PExp args))

pImplicitArg syn = do lchar '{'; n <- iName
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
pData syn = try (do reserved "data"; tyn <- pfName; ty <- pTSig syn
                    reserved "where"
                    ty' <- implicit syn tyn ty
                    cons <- sepBy (pConstructor syn) (lchar '|')
                    lchar ';'
                    return $ PData (PDatadecl tyn ty' cons))
        <|> do reserved "data"; tyn <- pfName; args <- many iName
               lchar '='
               cons <- sepBy1 (pSimpleCon syn) (lchar '|')
               lchar ';'
               let conty = mkPApp (PRef tyn) (map PRef args)
               let ty = bindArgs (map (\a -> PSet) args) PSet
               ty' <- implicit syn tyn ty
               cons' <- mapM (\ (x, cargs) -> do let cty = bindArgs cargs conty
                                                 cty' <- implicit syn x cty
                                                 return (x, cty')) cons
               return $ PData (PDatadecl tyn ty' cons')

mkPApp t [] = t
mkPApp t xs = PApp t (map PExp xs)

bindArgs :: [PTerm] -> PTerm -> PTerm
bindArgs [] t = t
bindArgs (x:xs) t = PPi Exp (MN 0 "t") x (bindArgs xs t)

pConstructor :: SyntaxInfo -> IParser (Name, PTerm)
pConstructor syn
    = do cn <- pfName; ty <- pTSig syn
         ty' <- implicit syn cn ty
         return (cn, ty')

pSimpleCon :: SyntaxInfo -> IParser (Name, [PTerm])
pSimpleCon syn 
     = do cn <- pfName
          args <- many (pSimpleExpr syn)
          return (cn, args)

--------- Pattern match clauses ---------

pPattern :: SyntaxInfo -> IParser PDecl
pPattern syn = do clause <- pClause syn
                  return (PClauses (MN 2 "_") [clause]) -- collect together later

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



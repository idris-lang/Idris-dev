module Idris.Parser where

import Idris.AbsSyntax

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
lchar = lexeme.char

parseExpr i = runParser (pFullExpr defaultSyntax) i "(input)"

parseProg :: SyntaxInfo -> String -> Idris [PDecl]
parseProg syn fname 
                = do file <- lift $ readFile fname
                     i <- get
                     case (runParser (do ps <- many1 (pDecl syn)
                                         eof
                                         i' <- getState
                                         return (concat ps, i')) i fname file) of
                        Left err -> fail (show err)
                        Right (x, i) -> do put i
                                           return (collect x)

-- Collect PClauses with the same function name
collect :: [PDecl] -> [PDecl]
collect (PClauses _ [c@(PClause n l r)] : ds) = clauses n [c] ds
  where clauses n acc (PClauses _ [c@(PClause n' l r)] : ds)
           | n == n' = clauses n (c : acc) ds
        clauses n acc xs = PClauses n (reverse acc) : collect xs
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
           lchar ';'
           i <- getState
           return [fmap (addImpl i) d]
    <|> try (pUsing syn)

--------- Top Level Declarations ---------

pDecl' :: SyntaxInfo -> IParser PDecl
pDecl' syn
       = try pFixity
     <|> try (do n <- pfName; ty <- pTSig syn
                 ty' <- implicit syn n ty
                 return (PTy n ty'))
     <|> try (pData syn)
     <|> try (pPattern syn)

pUsing :: SyntaxInfo -> IParser [PDecl]
pUsing syn = 
    do reserved "using"; 
       lchar '('
       ns <- sepBy1 (do x <- pfName; t <- pTSig syn; return (x,t))
                    (lchar ',')
       lchar ')'
       lchar '{'
       let uvars = using syn
       ds <- many1 (pDecl (syn { using = uvars ++ ns }))
       lchar '}'
       return (concat ds)

--------- Fixity ---------

pFixity :: IParser PDecl
pFixity = do f <- fixity; i <- natural; ops <- sepBy1 operator (lchar ',')
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
        <|> try (do reserved "Set"; return PSet)

pHSimpleExpr syn
             = try (pSimpleExpr syn)
           <|> do lchar '.'
                  e <- pSimpleExpr syn
                  return $ PHidden e

pApp syn = do f <- pSimpleExpr syn
              iargs <- many (pImplicitArg syn)
              args <- many1 (pSimpleExpr syn)
              return (PApp f iargs args)

pImplicitArg syn = do lchar '{'; n <- iName
                      v <- option (PRef n) (do lchar '='; pExpr syn)
                      lchar '}'
                      return (n, v)

pTSig syn = do lchar ':'
               pExpr syn

pLambda syn = do lchar '\\'; x <- iName; t <- option Placeholder (pTSig syn)
                 symbol "=>"
                 sc <- pExpr syn
                 return (PLam x t sc)

pPi syn = do lchar '('; x <- iName; t <- pTSig syn; lchar ')'
             symbol "->"
             sc <- pExpr syn
             return (PPi Exp x t sc)
      <|> do lchar '{'; x <- iName; t <- pTSig syn; lchar '}'
             symbol "->"
             sc <- pExpr syn
             return (PPi Imp x t sc)

table fixes 
   = toTable (reverse fixes) ++
      [[binary "="  (\x y -> PApp (PRef (UN ["="])) [] [x,y]) AssocLeft],
       [binary "->" (PPi Exp (MN 0 "X")) AssocRight]]

toTable fs = map (map toBin) 
                 (groupBy (\ (Fix x _) (Fix y _) -> prec x == prec y) fs)
   where toBin (Fix f op) = binary op 
                               (\x y -> PApp (PRef (UN [op])) [] [x,y]) (assoc f)
         assoc (Infixl _) = AssocLeft
         assoc (Infixr _) = AssocRight
         assoc (InfixN _) = AssocNone

binary name f assoc = Infix (do { reservedOp name; return f }) assoc

--------- Data declarations ---------

pData :: SyntaxInfo -> IParser PDecl
pData syn = try (do reserved "data"; tyn <- pfName; ty <- pTSig syn
                    reserved "where"
                    ty' <- implicit syn tyn ty
                    cons <- sepBy1 (pConstructor syn) (lchar '|')
                    return $ PData (PDatadecl tyn ty' cons))
        <|> do reserved "data"; tyn <- pfName; args <- many iName
               lchar '='
               cons <- sepBy1 (pSimpleCon syn) (lchar '|')
               let conty = mkPApp (PRef tyn) (map PRef args)
               let ty = bindArgs (map (\a -> PSet) args) PSet
               ty' <- implicit syn tyn ty
               cons' <- mapM (\ (x, cargs) -> do let cty = bindArgs cargs conty
                                                 cty' <- implicit syn x cty
                                                 return (x, cty')) cons
               return $ PData (PDatadecl tyn ty' cons')

mkPApp t [] = t
mkPApp t xs = PApp t [] xs

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
                  return (PClauses (MN 0 "_") [clause]) -- collect together later

pClause :: SyntaxInfo -> IParser PClause
pClause syn
        = try (do n <- pfName
                  iargs <- many (pImplicitArg syn)
                  args <- many (pHSimpleExpr syn)
                  lchar '='
                  rhs <- pExpr syn
                  return $ PClause n (PApp (PRef n) iargs args) rhs)
       <|> do l <- pSimpleExpr syn
              op <- operator
              let n = UN [op]
              r <- pSimpleExpr syn
              lchar '='
              rhs <- pExpr syn
              return $ PClause n (PApp (PRef n) [] [l,r]) rhs

-- Dealing with implicit arguments

implicit :: SyntaxInfo -> Name -> PTerm -> IParser PTerm
implicit syn n ptm 
    = do i <- getState
         let (tm', name_arity) = implicitise syn i ptm
         setState (i { idris_implicits = addDef n name_arity (idris_implicits i) })
         return tm'



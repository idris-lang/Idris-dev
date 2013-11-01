{-# LANGUAGE GeneralizedNewtypeDeriving, ConstraintKinds, PatternGuards #-}
module Idris.ParseData where

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
import Idris.ParseExpr
import Idris.DSL

import Core.TT
import Core.Evaluate

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

{- |Parses a record type declaration
Record ::=
    DocComment Accessibility? 'record' FnName TypeSig 'where' OpenBlock Constructor KeepTerminator CloseBlock;
-}
record :: SyntaxInfo -> IdrisParser PDecl
record syn = do (doc, acc) <- try (do
                      doc <- option "" (docComment '|')
                      acc <- optional accessibility
                      reserved "record"
                      return (doc, acc))
                fc <- getFC
                tyn_in <- fnName
                lchar ':'
                ty <- typeExpr (allowImp syn)
                let tyn = expandNS syn tyn_in
                reserved "where"
                (cdoc, cn, cty, _) <- indentedBlockS (constructor syn)
                accData acc tyn [cn]
                let rsyn = syn { syn_namespace = show (nsroot tyn) :
                                                    syn_namespace syn }
                let fns = getRecNames rsyn cty
                mapM_ (\n -> addAcc n acc) fns
                return $ PRecord doc rsyn fc tyn ty cdoc cn cty
             <?> "record type declaration"
  where
    getRecNames :: SyntaxInfo -> PTerm -> [Name]
    getRecNames syn (PPi _ n _ sc) = [expandNS syn n, expandNS syn (mkType n)]
                                       ++ getRecNames syn sc
    getRecNames _ _ = []

    toFreeze :: Maybe Accessibility -> Maybe Accessibility
    toFreeze (Just Frozen) = Just Hidden
    toFreeze x = x

{- | Parses data declaration type (normal or codata)
DataI ::= 'data' | 'codata';
-}
dataI :: IdrisParser Bool
dataI = do reserved "data"; return False
    <|> do reserved "codata"; return True

{- | Parses a data type declaration
Data ::= DocComment? Accessibility? DataI FnName TypeSig ExplicitTypeDataRest?
       | DocComment? Accessibility? DataI FnName Name*   DataRest?
       ;
Constructor' ::= Constructor KeepTerminator;
ExplicitTypeDataRest ::= 'where' OpenBlock Constructor'* CloseBlock;

DataRest ::= '=' SimpleConstructorList Terminator
            | 'where'!
           ;
SimpleConstructorList ::=
    SimpleConstructor
  | SimpleConstructor '|' SimpleConstructorList
  ;
-}
data_ :: SyntaxInfo -> IdrisParser PDecl
data_ syn = do (doc, acc, co) <- try (do
                    doc <- option "" (docComment '|')
                    pushIndent
                    acc <- optional accessibility
                    co <- dataI
                    return (doc, acc, co))
               fc <- getFC
               tyn_in <- fnName
               (do try (lchar ':')
                   popIndent
                   ty <- typeExpr (allowImp syn)
                   let tyn = expandNS syn tyn_in
                   option (PData doc syn fc co (PLaterdecl tyn ty)) (do
                     reserved "where"
                     cons <- indentedBlock (constructor syn)
                     accData acc tyn (map (\ (_, n, _, _) -> n) cons)
                     return $ PData doc syn fc co (PDatadecl tyn ty cons))) <|> (do
                    args <- many name
                    let ty = bindArgs (map (const PType) args) PType
                    let tyn = expandNS syn tyn_in
                    option (PData doc syn fc co (PLaterdecl tyn ty)) (do
                      try (lchar '=') <|> do reserved "where"
                                             let kw = (if co then "co" else "") ++ "data "
                                             let n  = show tyn_in ++ " "
                                             let s  = kw ++ n
                                             let as = concat (intersperse " " $ map show args) ++ " "
                                             let ns = concat (intersperse " -> " $ map ((\x -> "(" ++ x ++ " : Type)") . show) args)
                                             let ss = concat (intersperse " -> " $ map (const "Type") args)
                                             let fix1 = s ++ as ++ " = ..."
                                             let fix2 = s ++ ": " ++ ns ++ " -> Type where\n  ..."
                                             let fix3 = s ++ ": " ++ ss ++ " -> Type where\n  ..."
                                             fail $ fixErrorMsg "unexpected \"where\"" [fix1, fix2, fix3]
                      cons <- sepBy1 (simpleConstructor syn) (lchar '|')
                      terminator
                      let conty = mkPApp fc (PRef fc tyn) (map (PRef fc) args)
                      cons' <- mapM (\ (doc, x, cargs, cfc) ->
                                   do let cty = bindArgs cargs conty
                                      return (doc, x, cty, cfc)) cons
                      accData acc tyn (map (\ (_, n, _, _) -> n) cons')
                      return $ PData doc syn fc co (PDatadecl tyn ty cons')))
           <?> "data type declaration"
  where
    mkPApp :: FC -> PTerm -> [PTerm] -> PTerm
    mkPApp fc t [] = t
    mkPApp fc t xs = PApp fc t (map pexp xs)
    bindArgs :: [PTerm] -> PTerm -> PTerm
    bindArgs xs t = foldr (PPi expl (MN 0 "t")) t xs


{- | Parses a type constructor declaration
  Constructor ::= DocComment? FnName TypeSig;
-}
constructor :: SyntaxInfo -> IdrisParser (String, Name, PTerm, FC)
constructor syn
    = do doc <- option "" (docComment '|')
         cn_in <- fnName; fc <- getFC
         let cn = expandNS syn cn_in
         lchar ':'
         ty <- typeExpr (allowImp syn)
         return (doc, cn, ty, fc)
      <?> "constructor"

{- | Parses a constructor for simple discriminative union data types
  SimpleConstructor ::= FnName SimpleExpr* DocComment?
-}
simpleConstructor :: SyntaxInfo -> IdrisParser (String, Name, [PTerm], FC)
simpleConstructor syn
     = do cn_in <- fnName
          let cn = expandNS syn cn_in
          fc <- getFC
          args <- many (do notEndApp
                           simpleExpr syn)
          doc <- option "" (docComment '^')
          return (doc, cn, args, fc)
       <?> "constructor"

{- | Parses a dsl block declaration
DSL ::= 'dsl' FnName OpenBlock Overload'+ CloseBlock;
 -}
dsl :: SyntaxInfo -> IdrisParser PDecl
dsl syn = do reserved "dsl"
             n <- fnName
             bs <- indentedBlock (overload syn)
             let dsl = mkDSL bs (dsl_info syn)
             checkDSL dsl
             i <- get
             put (i { idris_dsls = addDef n dsl (idris_dsls i) })
             return (PDSL n dsl)
          <?> "dsl block declaration"
    where mkDSL :: [(String, PTerm)] -> DSL -> DSL
          mkDSL bs dsl = let var    = lookup "variable" bs
                             first  = lookup "index_first" bs
                             next   = lookup "index_next" bs
                             leto   = lookup "let" bs
                             lambda = lookup "lambda" bs in
                             initDSL { dsl_var = var,
                                       index_first = first,
                                       index_next = next,
                                       dsl_lambda = lambda,
                                       dsl_let = leto }

{- | Checks DSL for errors -}
-- FIXME: currently does nothing, check if DSL is really sane
checkDSL :: DSL -> IdrisParser ()
checkDSL dsl = return ()

{- | Parses a DSL overload declaration
OverloadIdentifier ::= 'let' | Identifier;
Overload ::= OverloadIdentifier '=' Expr;
-}
overload :: SyntaxInfo -> IdrisParser (String, PTerm)
overload syn = do o <- identifier <|> do reserved "let"
                                         return "let"
                  if o `notElem` overloadable
                     then fail $ show o ++ " is not an overloading"
                     else do
                       lchar '='
                       t <- expr syn
                       return (o, t)
               <?> "dsl overload declaratioN"
    where overloadable = ["let","lambda","index_first","index_next","variable"]



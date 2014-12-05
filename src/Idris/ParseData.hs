{-# LANGUAGE GeneralizedNewtypeDeriving, ConstraintKinds, PatternGuards #-}
module Idris.ParseData where

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
import Idris.ParseExpr
import Idris.DSL

import Idris.Core.TT
import Idris.Core.Evaluate

import Idris.Docstrings

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

type RecordCtor = (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, PTerm, FC, [Name])

{- |Parses a record type declaration
Record ::=
    DocComment Accessibility? 'record' FnName TypeSig 'where' OpenBlock Constructor KeepTerminator CloseBlock;
-}
record :: SyntaxInfo -> IdrisParser PDecl
record syn = do (doc, argDocs, acc, opts) <- try (do
                      (doc, argDocs) <- option noDocs docComment
                      ist <- get
                      let doc' = annotCode (tryFullExpr syn ist) doc
                          argDocs' = [ (n, annotCode (tryFullExpr syn ist) d)
                                     | (n, d) <- argDocs ]
                      acc <- optional accessibility
                      opts <- dataOpts []
                      reserved "record"
                      return (doc', argDocs', acc, opts))
                fc <- getFC
                tyn_in <- fnName
                lchar ':'
                ty <- typeExpr (allowImp syn)
                let tyn = expandNS syn tyn_in
                reserved "where"
                (cdoc, cargDocs, cn, cty, _, _) <- indentedBlockS (agdaStyleBody syn tyn ty <|> constructor syn)
                accData acc tyn [cn]
                let rsyn = syn { syn_namespace = show (nsroot tyn) :
                                                    syn_namespace syn }
                let fns = getRecNames rsyn cty
                mapM_ (\n -> addAcc n acc) fns
                return $ PRecord doc rsyn fc tyn ty opts cdoc cn cty
             <?> "record type declaration"
  where
    getRecNames :: SyntaxInfo -> PTerm -> [Name]
    getRecNames syn (PPi _ n _ sc) = [expandNS syn n, expandNS syn (mkType n)]
                                       ++ getRecNames syn sc
    getRecNames _ _ = []

    toFreeze :: Maybe Accessibility -> Maybe Accessibility
    toFreeze (Just Frozen) = Just Hidden
    toFreeze x = x
    
    agdaStyleBody :: SyntaxInfo -> Name -> PTerm -> IdrisParser RecordCtor
    agdaStyleBody syn recName recType = do
        ist <- get
        fc  <- getFC

        let ctorDoc = parseDocstring . T.pack $ "Constructor of " ++ show recName
        ctorName <- reserved "constructor" *> fnName

        fields <- many $ do
            (doc, argDocs) <- option noDocs docComment

            let expField = do
                    n <- fnName <* lchar ':'
                    t <- typeExpr (allowImp syn)
                    return (n, t, expl)

            let impField = do
                    symbol "{"
                    n <- fnName <* lchar ':'
                    t <- typeExpr (allowImp syn)
                    symbol "}"
                    return (n, t, impl)

            (n, t, plicity) <- impField <|> expField

            return (n, t, plicity, doc, argDocs)

        let ctorDoc' = annotate syn ist ctorDoc
        let fieldDocs = [(n, annotate syn ist doc) | (n, t, p, doc, argDocs) <- fields]
        let target = PApp fc (PRef fc recName) (getParams fc recType)
        let ctorType = mkCtorType target [(p, n, t) | (n, t, p, doc, argDocs) <- fields]

        return (ctorDoc', fieldDocs, ctorName, ctorType, fc, [])

    mkCtorType :: PTerm -> [(Plicity, Name, PTerm)] -> PTerm
    mkCtorType = foldr $ uncurry3 PPi

    getParams :: FC -> PTerm -> [PArg]
    getParams fc (PPi (Exp os _ _) n t ts) = (PExp 0 os n $ PRef fc n) : getParams fc ts
    getParams fc (PPi (Imp os _ _) n t ts) = (PImp 0 False os n $ PRef fc n) : getParams fc ts
    getParams _ _ = []

    annotate :: SyntaxInfo -> IState -> Docstring () -> Docstring (Either Err PTerm)
    annotate syn ist = annotCode $ tryFullExpr syn ist

    uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
    uncurry3 f (x, y, z) = f x y z

{- | Parses data declaration type (normal or codata)
DataI ::= 'data' | 'codata';
-}
dataI :: IdrisParser DataOpts
dataI = do reserved "data"; return []
    <|> do reserved "codata"; return [Codata]

{- | Parses if a data should not have a default eliminator
DefaultEliminator ::= 'noelim'?
 -}
dataOpts :: DataOpts -> IdrisParser DataOpts
dataOpts opts
    = do reserved "%elim"; dataOpts (DefaultEliminator : DefaultCaseFun : opts)
  <|> do reserved "%case"; dataOpts (DefaultCaseFun : opts)
  <|> do reserved "%error_reverse"; dataOpts (DataErrRev : opts)
  <|> return opts
  <?> "data options"

{- | Parses a data type declaration
Data ::= DocComment? Accessibility? DataI DefaultEliminator FnName TypeSig ExplicitTypeDataRest?
       | DocComment? Accessibility? DataI DefaultEliminator FnName Name*   DataRest?
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
data_ syn = do (doc, argDocs, acc, dataOpts) <- try (do
                    (doc, argDocs) <- option noDocs docComment
                    pushIndent
                    acc <- optional accessibility
                    elim <- dataOpts []
                    co <- dataI
                    ist <- get
                    let dataOpts = combineDataOpts (elim ++ co)
                        doc' = annotCode (tryFullExpr syn ist) doc
                        argDocs' = [ (n, annotCode (tryFullExpr syn ist) d)
                                   | (n, d) <- argDocs ]
                    return (doc', argDocs', acc, dataOpts))
               fc <- getFC
               tyn_in <- fnName
               (do try (lchar ':')
                   popIndent
                   ty <- typeExpr (allowImp syn)
                   let tyn = expandNS syn tyn_in
                   option (PData doc argDocs syn fc dataOpts (PLaterdecl tyn ty)) (do
                     reserved "where"
                     cons <- indentedBlock (constructor syn)
                     accData acc tyn (map (\ (_, _, n, _, _, _) -> n) cons)
                     return $ PData doc argDocs syn fc dataOpts (PDatadecl tyn ty cons))) <|> (do
                    args <- many name
                    let ty = bindArgs (map (const PType) args) PType
                    let tyn = expandNS syn tyn_in
                    option (PData doc argDocs syn fc dataOpts (PLaterdecl tyn ty)) (do
                      try (lchar '=') <|> do reserved "where"
                                             let kw = (if DefaultEliminator `elem` dataOpts then "%elim" else "") ++ (if Codata `elem` dataOpts then "co" else "") ++ "data "
                                             let n  = show tyn_in ++ " "
                                             let s  = kw ++ n
                                             let as = concat (intersperse " " $ map show args) ++ " "
                                             let ns = concat (intersperse " -> " $ map ((\x -> "(" ++ x ++ " : Type)") . show) args)
                                             let ss = concat (intersperse " -> " $ map (const "Type") args)
                                             let fix1 = s ++ as ++ " = ..."
                                             let fix2 = s ++ ": " ++ ns ++ " -> Type where\n  ..."
                                             let fix3 = s ++ ": " ++ ss ++ " -> Type where\n  ..."
                                             fail $ fixErrorMsg "unexpected \"where\"" [fix1, fix2, fix3]
                      cons <- sepBy1 (simpleConstructor syn) (reservedOp "|")
                      terminator
                      let conty = mkPApp fc (PRef fc tyn) (map (PRef fc) args)
                      cons' <- mapM (\ (doc, argDocs, x, cargs, cfc, fs) ->
                                   do let cty = bindArgs cargs conty
                                      return (doc, argDocs, x, cty, cfc, fs)) cons
                      accData acc tyn (map (\ (_, _, n, _, _, _) -> n) cons')
                      return $ PData doc argDocs syn fc dataOpts (PDatadecl tyn ty cons')))
           <?> "data type declaration"
  where
    mkPApp :: FC -> PTerm -> [PTerm] -> PTerm
    mkPApp fc t [] = t
    mkPApp fc t xs = PApp fc t (map pexp xs)
    bindArgs :: [PTerm] -> PTerm -> PTerm
    bindArgs xs t = foldr (PPi expl (sMN 0 "_t")) t xs
    combineDataOpts :: DataOpts -> DataOpts
    combineDataOpts opts = if Codata `elem` opts
                              then delete DefaultEliminator opts
                              else opts


{- | Parses a type constructor declaration
  Constructor ::= DocComment? FnName TypeSig;
-}
constructor :: SyntaxInfo -> IdrisParser (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, PTerm, FC, [Name])
constructor syn
    = do (doc, argDocs) <- option noDocs docComment
         cn_in <- fnName; fc <- getFC
         let cn = expandNS syn cn_in
         lchar ':'
         fs <- option [] (do lchar '%'; reserved "erase"
                             sepBy1 name (lchar ','))
         ty <- typeExpr (allowImp syn)
         ist <- get
         let doc' = annotCode (tryFullExpr syn ist) doc
             argDocs' = [ (n, annotCode (tryFullExpr syn ist) d)
                        | (n, d) <- argDocs ]
         return (doc', argDocs', cn, ty, fc, fs)
      <?> "constructor"

{- | Parses a constructor for simple discriminated union data types
  SimpleConstructor ::= FnName SimpleExpr* DocComment?
-}
simpleConstructor :: SyntaxInfo -> IdrisParser (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, [PTerm], FC, [Name])
simpleConstructor syn
     = do (doc, _) <- option noDocs (try docComment)
          ist <- get
          let doc' = annotCode (tryFullExpr syn ist) doc
          cn_in <- fnName
          let cn = expandNS syn cn_in
          fc <- getFC
          args <- many (do notEndApp
                           simpleExpr syn)
          return (doc', [], cn, args, fc, [])
       <?> "constructor"

{- | Parses a dsl block declaration
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
                             lambda = lookup "lambda" bs
                             pi     = lookup "pi" bs in
                             initDSL { dsl_var = var,
                                       index_first = first,
                                       index_next = next,
                                       dsl_lambda = lambda,
                                       dsl_let = leto,
                                       dsl_pi = pi }

{- | Checks DSL for errors -}
-- FIXME: currently does nothing, check if DSL is really sane
--
-- Issue #1595 on the Issue Tracker
--
--     https://github.com/idris-lang/Idris-dev/issues/1595
--
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
    where overloadable = ["let","lambda","pi","index_first","index_next","variable"]

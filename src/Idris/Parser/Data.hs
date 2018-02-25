{-|
Module      : Idris.Parser.Data
Description : Parse Data declarations.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, PatternGuards #-}
module Idris.Parser.Data where

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.Docstrings
import Idris.Options
import Idris.Parser.Expr
import Idris.Parser.Helpers
import Idris.Parser.Ops

import Prelude hiding (pi)

import Control.Applicative
import Control.Monad.State.Strict
import Data.List
import Data.Maybe
import Text.Megaparsec ((<?>))
import qualified Text.Megaparsec as P

{- | Parses a record type declaration
Record ::=
    DocComment Accessibility? 'record' FnName TypeSig 'where' OpenBlock Constructor KeepTerminator CloseBlock;
-}
record :: SyntaxInfo -> IdrisParser PDecl
record syn = (appExtent $ do
                (doc, paramDocs, acc, opts) <- P.try (do
                      (doc, paramDocs) <- P.option noDocs docComment
                      ist <- get
                      let doc' = annotCode (tryFullExpr syn ist) doc
                          paramDocs' = [ (n, annotCode (tryFullExpr syn ist) d)
                                     | (n, d) <- paramDocs ]
                      acc <- accessibility
                      opts <- dataOpts []
                      co <- recordI
                      return (doc', paramDocs', acc, opts ++ co))
                (tyn_in, nfc) <- withExtent fnName
                let tyn = expandNS syn tyn_in
                let rsyn = syn { syn_namespace = show (nsroot tyn) :
                                                    syn_namespace syn }
                params <- P.manyTill (recordParameter rsyn) (keyword "where")
                (fields, cname, cdoc) <- indentedBlockS $ recordBody rsyn tyn
                let fnames = map (expandNS rsyn) (mapMaybe getName fields)
                case cname of
                     Just cn' -> accData acc tyn (fst cn' : fnames)
                     Nothing -> return ()
                return $ \fc -> PRecord doc rsyn fc opts tyn nfc params paramDocs fields cname cdoc syn)
              <?> "record type declaration"
  where
    getName (Just (n, _), _, _, _) = Just n
    getName _ = Nothing

    recordBody :: SyntaxInfo -> Name -> IdrisParser ([((Maybe (Name, FC)), Plicity, PTerm, Maybe (Docstring (Either Err PTerm)))], Maybe (Name, FC), Docstring (Either Err PTerm))
    recordBody syn tyn = do
        ist <- get

        (constructorName, constructorDoc) <- P.option (Nothing, emptyDocstring)
                                             (do (doc, _) <- P.option noDocs docComment
                                                 n <- withExtent constructor
                                                 return (Just n, doc))

        let constructorDoc' = annotate syn ist constructorDoc

        fields <- many . indented $ fieldLine syn

        return (concat fields, constructorName, constructorDoc')
      where
        fieldLine :: SyntaxInfo -> IdrisParser [(Maybe (Name, FC), Plicity, PTerm, Maybe (Docstring (Either Err PTerm)))]
        fieldLine syn = do
            doc <- optional docComment
            c <- optional $ lchar '{'
            let oneName = (do (n, nfc) <- withExtent fnName
                              return $ Just (expandNS syn n, nfc))
                          <|> (symbol "_" >> return Nothing)
            ns <- commaSeparated oneName
            lchar ':'
            -- Implicits are scoped in fields (fields aren't top level)
            t <- typeExpr (scopedImp syn)
            p <- endPlicity c
            ist <- get
            let doc' = case doc of -- Temp: Throws away any possible arg docs
                        Just (d,_) -> Just $ annotate syn ist d
                        Nothing    -> Nothing
            return $ map (\n -> (n, p, t, doc')) ns

        constructor :: (Parsing m, MonadState IState m) => m Name
        constructor = keyword "constructor" *> fnName

        endPlicity :: Maybe Char -> IdrisParser Plicity
        endPlicity (Just _) = do lchar '}'
                                 return impl
        endPlicity Nothing = return expl

        annotate :: SyntaxInfo -> IState -> Docstring () -> Docstring (Either Err PTerm)
        annotate syn ist = annotCode $ tryFullExpr syn ist

recordParameter :: SyntaxInfo -> IdrisParser (Name, FC, Plicity, PTerm)
recordParameter syn =
  (do lchar '('
      (n, nfc, pt) <- (namedTy syn <|> onlyName syn)
      lchar ')'
      return (n, nfc, expl, pt))
  <|>
  (do (n, nfc, pt) <- onlyName syn
      return (n, nfc, expl, pt))
  where
    namedTy :: SyntaxInfo -> IdrisParser (Name, FC, PTerm)
    namedTy syn =
      do (n, nfc) <- withExtent fnName
         lchar ':'
         ty <- typeExpr (allowImp syn)
         return (expandNS syn n, nfc, ty)
    onlyName :: SyntaxInfo -> IdrisParser (Name, FC, PTerm)
    onlyName syn =
      do (n, nfc) <- withExtent fnName
         return (expandNS syn n, nfc, PType nfc)

{- | Parses data declaration type (normal or codata)
DataI ::= 'data' | 'codata';
-}
dataI :: IdrisParser DataOpts
dataI = do keyword "data"; return []
    <|> do keyword "codata"; return [Codata]

recordI :: IdrisParser DataOpts
recordI = do keyword "record"; return []
          <|> do keyword "corecord"; return [Codata]

dataOpts :: DataOpts -> IdrisParser DataOpts
dataOpts opts =
      do reserved "%error_reverse"; dataOpts (DataErrRev : opts)
  <|> return opts
  <?> "data options"

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
data_ syn = (checkDeclFixity $
            do (doc, argDocs, acc, dataOpts) <- P.try (do
                    (doc, argDocs) <- P.option noDocs docComment
                    pushIndent
                    acc <- accessibility
                    errRev <- dataOpts []
                    co <- dataI
                    ist <- get
                    let dataOpts = errRev ++ co
                        doc' = annotCode (tryFullExpr syn ist) doc
                        argDocs' = [ (n, annotCode (tryFullExpr syn ist) d)
                                   | (n, d) <- argDocs ]
                    return (doc', argDocs', acc, dataOpts))
               (tyn_in, nfc) <- withExtent fnName
               (do P.try (lchar ':')
                   ty <- typeExpr (allowImp syn)
                   let tyn = expandNS syn tyn_in
                   d <- P.option (PData doc argDocs syn nfc dataOpts (PLaterdecl tyn nfc ty)) (do
                     keyword "where"
                     cons <- indentedBlock (constructor syn)
                     accData acc tyn (map (\ (_, _, n, _, _, _, _) -> n) cons)
                     return $ PData doc argDocs syn nfc dataOpts (PDatadecl tyn nfc ty cons))
                   terminator
                   return d) <|> (do
                    args <- many (do notEndApp
                                     x <- name
                                     return x)
                    let ty = bindArgs (map (const (PType nfc)) args) (PType nfc)
                    let tyn = expandNS syn tyn_in
                    d <- P.option (PData doc argDocs syn nfc dataOpts (PLaterdecl tyn nfc ty)) (do
                      P.try (lchar '=') <|> do keyword "where"
                                               let kw = (if Codata `elem` dataOpts then "co" else "") ++ "data "
                                               let n  = show tyn_in ++ " "
                                               let s  = kw ++ n
                                               let as = unwords (map show args) ++ " "
                                               let ns = concat (intersperse " -> " $ map ((\x -> "(" ++ x ++ " : Type)") . show) args)
                                               let ss = concat (intersperse " -> " $ map (const "Type") args)
                                               let fix1 = s ++ as ++ " = ..."
                                               let fix2 = s ++ ": " ++ ns ++ " -> Type where\n  ..."
                                               let fix3 = s ++ ": " ++ ss ++ " -> Type where\n  ..."
                                               fail $ fixErrorMsg "unexpected \"where\"" [fix1, fix2, fix3]
                      cons <- P.sepBy1 (simpleConstructor (syn { withAppAllowed = False })) (reservedOp "|")
                      let conty = mkPApp nfc (PRef nfc [] tyn) (map (PRef nfc []) args)
                      cons' <- mapM (\ (doc, argDocs, x, xfc, cargs, cfc, fs) ->
                                   do let cty = bindArgs cargs conty
                                      return (doc, argDocs, x, xfc, cty, cfc, fs)) cons
                      accData acc tyn (map (\ (_, _, n, _, _, _, _) -> n) cons')
                      return $ PData doc argDocs syn nfc dataOpts (PDatadecl tyn nfc ty cons'))
                    terminator
                    return d))
           <?> "data type declaration"
  where
    mkPApp :: FC -> PTerm -> [PTerm] -> PTerm
    mkPApp fc t [] = t
    mkPApp fc t xs = PApp fc t (map pexp xs)
    bindArgs :: [PTerm] -> PTerm -> PTerm
    bindArgs xs t = foldr (PPi expl (sMN 0 "_t") NoFC) t xs


{- | Parses a type constructor declaration
  Constructor ::= DocComment? FnName TypeSig;
-}
constructor :: SyntaxInfo -> IdrisParser (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, FC, PTerm, FC, [Name])
constructor syn
    = do (doc, argDocs) <- P.option noDocs docComment
         (cn_in, nfc) <- withExtent fnName
         let cn = expandNS syn cn_in
         lchar ':'
         fs <- P.option [] (do lchar '%'; reserved "erase"
                               P.sepBy1 name (lchar ','))
         (ty, fc) <- withExtent $ typeExpr (allowImp syn)
         ist <- get
         let doc' = annotCode (tryFullExpr syn ist) doc
             argDocs' = [ (n, annotCode (tryFullExpr syn ist) d)
                        | (n, d) <- argDocs ]
         checkNameFixity cn
         return (doc', argDocs', cn, nfc, ty, fc, fs)
      <?> "constructor"

{- | Parses a constructor for simple discriminated union data types
  SimpleConstructor ::= FnName SimpleExpr* DocComment?
-}
simpleConstructor :: SyntaxInfo -> IdrisParser (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, FC, [PTerm], FC, [Name])
simpleConstructor syn
     = (appExtent $ do
          (doc, _) <- P.option noDocs (P.try docComment)
          ist <- get
          let doc' = annotCode (tryFullExpr syn ist) doc
          (cn_in, nfc) <- withExtent fnName
          let cn = expandNS syn cn_in
          args <- many (do notEndApp
                           simpleExpr syn)
          checkNameFixity cn
          return $ \fc -> (doc', [], cn, nfc, args, fc, []))
        <?> "constructor"
{- | Parses a dsl block declaration
DSL ::= 'dsl' FnName OpenBlock Overload'+ CloseBlock;
 -}
dsl :: SyntaxInfo -> IdrisParser PDecl
dsl syn = do keyword "dsl"
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
overload syn = do o <- highlight AnnKeyword $ identifier <|> "let" <$ reserved "let"
                  if o `notElem` overloadable
                     then fail $ show o ++ " is not an overloading"
                     else do
                       lchar '='
                       t <- expr syn
                       return (o, t)
               <?> "dsl overload declaratioN"
    where overloadable = ["let","lambda","pi","index_first","index_next","variable"]

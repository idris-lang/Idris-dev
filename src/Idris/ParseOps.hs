{-# LANGUAGE GeneralizedNewtypeDeriving, ConstraintKinds, PatternGuards #-}
module Idris.ParseOps where

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

import Core.TT

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

{- |Creates table for fixity declarations to build expression parser using
  pre-build and user-defined operator/fixity declarations -}
table :: [FixDecl] -> OperatorTable IdrisParser PTerm
table fixes
   = [[prefix "-" (\fc x -> PApp fc (PRef fc (UN "-"))
        [pexp (PApp fc (PRef fc (UN "fromInteger")) [pexp (PConstant (BI 0))]), pexp x])]]
       ++ toTable (reverse fixes) ++
      [[backtick],
       [binary "="  PEq AssocLeft],
       [binary "->" (\fc x y -> PPi expl (MN 42 "__pi_arg") x y) AssocRight]]

{- |Calculates table for fixtiy declarations -}
toTable :: [FixDecl] -> OperatorTable IdrisParser PTerm
toTable fs = map (map toBin)
                 (groupBy (\ (Fix x _) (Fix y _) -> prec x == prec y) fs)
   where toBin (Fix (PrefixN _) op) = prefix op
                                       (\fc x -> PApp fc (PRef fc (UN op)) [pexp x])
         toBin (Fix f op)
            = binary op (\fc x y -> PApp fc (PRef fc (UN op)) [pexp x,pexp y]) (assoc f)
         assoc (Infixl _) = AssocLeft
         assoc (Infixr _) = AssocRight
         assoc (InfixN _) = AssocNone

{- |Binary operator -}
binary :: String -> (FC -> PTerm -> PTerm -> PTerm) -> Assoc -> Operator IdrisParser PTerm
binary name f = Infix (do fc <- getFC
                          reservedOp name
                          doc <- option "" (docComment '^')
                          return (f fc))

{- |Prefix operator -}
prefix :: String -> (FC -> PTerm -> PTerm) -> Operator IdrisParser PTerm
prefix name f = Prefix (do reservedOp name
                           fc <- getFC
                           return (f fc))

{- |Backtick operator -}
backtick :: Operator IdrisParser PTerm
backtick = Infix (do lchar '`'; n <- fnName
                     lchar '`'
                     fc <- getFC
                     return (\x y -> PApp fc (PRef fc n) [pexp x, pexp y])) AssocNone

{- | Parses an operator in function position i.e. enclosed by `()', with an
 optional namespace

  OperatorFront ::= (Identifier_t '.')? '(' Operator_t ')';
-}
operatorFront :: IdrisParser Name
operatorFront = maybeWithNS (lchar '(' *> operator <* lchar ')') False []

{- | Parses a function (either normal name or operator)
  FnName ::= Name | OperatorFront;
-}
fnName :: IdrisParser Name
fnName = try operatorFront <|> name <?> "function name"


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

import Idris.Core.TT

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

-- | Creates table for fixity declarations to build expression parser
-- using pre-build and user-defined operator/fixity declarations
table :: [FixDecl] -> OperatorTable IdrisParser PTerm
table fixes
   = [[prefix "-" (\fc x -> PApp fc (PRef fc (sUN "-"))
        [pexp (PApp fc (PRef fc (sUN "fromInteger")) [pexp (PConstant (BI 0))]), pexp x])]]
       ++ toTable (reverse fixes) ++
      [[backtick],
       [binary "$" (\fc x y -> PApp fc x [pexp y]) AssocRight],
       [binary "="  PEq AssocLeft],
       [binary "->" (\fc x y -> PPi expl (sMN 42 "__pi_arg") x y) AssocRight]]

-- | Calculates table for fixtiy declarations
toTable :: [FixDecl] -> OperatorTable IdrisParser PTerm
toTable fs = map (map toBin)
                 (groupBy (\ (Fix x _) (Fix y _) -> prec x == prec y) fs)
   where toBin (Fix (PrefixN _) op) = prefix op
                                       (\fc x -> PApp fc (PRef fc (sUN op)) [pexp x])
         toBin (Fix f op)
            = binary op (\fc x y -> PApp fc (PRef fc (sUN op)) [pexp x,pexp y]) (assoc f)
         assoc (Infixl _) = AssocLeft
         assoc (Infixr _) = AssocRight
         assoc (InfixN _) = AssocNone

-- | Binary operator
binary :: String -> (FC -> PTerm -> PTerm -> PTerm) -> Assoc -> Operator IdrisParser PTerm
binary name f = Infix (do fc <- getFC
                          indentPropHolds gtProp
                          reservedOp name
                          indentPropHolds gtProp
                          doc <- option "" (docComment '^')
                          return (f fc))

-- | Prefix operator
prefix :: String -> (FC -> PTerm -> PTerm) -> Operator IdrisParser PTerm
prefix name f = Prefix (do reservedOp name
                           fc <- getFC
                           indentPropHolds gtProp
                           return (f fc))

-- | Backtick operator
backtick :: Operator IdrisParser PTerm
backtick = Infix (do indentPropHolds gtProp
                     lchar '`'; n <- fnName
                     lchar '`'
                     indentPropHolds gtProp
                     fc <- getFC
                     return (\x y -> PApp fc (PRef fc n) [pexp x, pexp y])) AssocNone

{- | Parses an operator in function position i.e. enclosed by `()', with an
 optional namespace

@
  OperatorFront ::= (Identifier_t '.')? '(' Operator_t ')';
@

-}
operatorFront :: IdrisParser Name
operatorFront = maybeWithNS (lchar '(' *> operator <* lchar ')') False []

{- | Parses a function (either normal name or operator)

@
  FnName ::= Name | OperatorFront;
@
-}
fnName :: IdrisParser Name
fnName = try operatorFront <|> name <?> "function name"

{- | Parses a fixity declaration
@
Fixity ::=
  FixityType Natural_t OperatorList Terminator
  ;
@
-}
fixity :: IdrisParser PDecl
fixity = do pushIndent
            f <- fixityType; i <- natural; ops <- sepBy1 operator (lchar ',')
            terminator
            let prec = fromInteger i
            istate <- get
            let infixes = idris_infixes istate
            let fs      = map (Fix (f prec)) ops
            let redecls = map (alreadyDeclared infixes) fs
            let ill     = filter (not . checkValidity) redecls
            if null ill
               then do put (istate { idris_infixes = nub $ sort (fs ++ infixes)
                                     , ibc_write     = map IBCFix fs ++ ibc_write istate
                                   })
                       fc <- getFC
                       return (PFix fc (f prec) ops)
               else fail $ concatMap (\(f, (x:xs)) -> "Illegal redeclaration of fixity:\n\t\""
                                                ++ show f ++ "\" overrides \"" ++ show x ++ "\"") ill
         <?> "fixity declaration"
             where alreadyDeclared :: [FixDecl] -> FixDecl -> (FixDecl, [FixDecl])
                   alreadyDeclared fs f = (f, filter ((extractName f ==) . extractName) fs)

                   checkValidity :: (FixDecl, [FixDecl]) -> Bool
                   checkValidity (f, fs) = all (== f) fs

                   extractName :: FixDecl -> String
                   extractName (Fix _ n) = n

{- | Parses a fixity declaration type (i.e. infix or prefix, associtavity)
@
    FixityType ::=
      'infixl'
      | 'infixr'
      | 'infix'
      | 'prefix'
      ;
@
 -}
fixityType :: IdrisParser (Int -> Fixity)
fixityType = do reserved "infixl"; return Infixl
         <|> do reserved "infixr"; return Infixr
         <|> do reserved "infix";  return InfixN
         <|> do reserved "prefix"; return PrefixN
         <?> "fixity type"


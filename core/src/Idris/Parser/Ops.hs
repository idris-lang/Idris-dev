{-|
Module      : Idris.Parser.Ops
Description : Parser for operators and fixity declarations.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE ConstraintKinds, GeneralizedNewtypeDeriving, PatternGuards #-}
module Idris.Parser.Ops where

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.Parser.Helpers

import Prelude hiding (pi)

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import qualified Data.ByteString.UTF8 as UTF8
import Data.Char
import qualified Data.HashSet as HS
import Data.List
import qualified Data.List.Split as Spl
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T
import Debug.Trace
import qualified Text.Parser.Char as Chr
import Text.Parser.Expression
import Text.Parser.LookAhead
import qualified Text.Parser.Token as Tok
import qualified Text.Parser.Token.Highlight as Hi
import Text.Trifecta hiding (char, charLiteral, natural, span, string,
                      stringLiteral, symbol, whiteSpace)
import Text.Trifecta.Delta

-- | Creates table for fixity declarations to build expression parser
-- using pre-build and user-defined operator/fixity declarations
table :: [FixDecl] -> OperatorTable IdrisParser PTerm
table fixes
   = [[prefix "-" (\fc x -> PApp fc (PRef fc [fc] (sUN "negate")) [pexp x])]] ++
      toTable (reverse fixes) ++
     [[backtick],
      [binary "$" (\fc x y -> flatten $ PApp fc x [pexp y]) AssocRight],
      [binary "="  (\fc x y -> PApp fc (PRef fc [fc] eqTy) [pexp x, pexp y]) AssocLeft],
      [nofixityoperator]]
  where
    flatten :: PTerm -> PTerm -- flatten application
    flatten (PApp fc (PApp _ f as) bs) = flatten (PApp fc f (as ++ bs))
    flatten t = t


-- | Calculates table for fixity declarations
toTable :: [FixDecl] -> OperatorTable IdrisParser PTerm
toTable fs = map (map toBin)
                 (groupBy (\ (Fix x _) (Fix y _) -> prec x == prec y) fs)
   where toBin (Fix (PrefixN _) op) = prefix op
                                       (\fc x -> PApp fc (PRef fc [] (sUN op)) [pexp x])
         toBin (Fix f op)
            = binary op (\fc x y -> PApp fc (PRef fc [] (sUN op)) [pexp x,pexp y]) (assoc f)
         assoc (Infixl _) = AssocLeft
         assoc (Infixr _) = AssocRight
         assoc (InfixN _) = AssocNone

-- | Binary operator
binary :: String -> (FC -> PTerm -> PTerm -> PTerm) -> Assoc -> Operator IdrisParser PTerm
binary name f = Infix (do indentPropHolds gtProp
                          fc <- reservedOpFC name
                          indentPropHolds gtProp
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
                     lchar '`'; (n, fc) <- fnName
                     lchar '`'
                     indentPropHolds gtProp
                     return (\x y -> PApp fc (PRef fc [fc] n) [pexp x, pexp y])) AssocNone

-- | Operator without fixity (throws an error)
nofixityoperator :: Operator IdrisParser PTerm
nofixityoperator = Infix (do indentPropHolds gtProp
                             op <- try operator
                             unexpected $ "Operator without known fixity: " ++ op) AssocNone


{- | Parses an operator in function position i.e. enclosed by `()', with an
 optional namespace

@
  OperatorFront ::=
    '(' '=' ')'
    | (Identifier_t '.')? '(' Operator_t ')'
    ;
@

-}
operatorFront :: IdrisParser (Name, FC)
operatorFront = try (do (FC f (l, c) _) <- getFC
                        op <- lchar '(' *> reservedOp "="  <* lchar ')'
                        return (eqTy, FC f (l, c) (l, c+3)))
            <|> maybeWithNS (do (FC f (l, c) _) <- getFC
                                op <- lchar '(' *> operator
                                (FC _ _ (l', c')) <- getFC
                                lchar ')'
                                return (op, (FC f (l, c) (l', c' + 1)))) False []

{- | Parses a function (either normal name or operator)

@
  FnName ::= Name | OperatorFront;
@
-}
fnName :: IdrisParser (Name, FC)
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
            f <- fixityType; i <- fst <$> natural;
            ops <- sepBy1 operator (lchar ',')
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

-- | Check that a declaration of an operator also has fixity declared
checkDeclFixity :: IdrisParser PDecl -> IdrisParser PDecl
checkDeclFixity p = do decl <- p
                       case getDeclName decl of
                         Nothing -> return decl
                         Just n -> do checkNameFixity n
                                      return decl
  where getDeclName (PTy _ _ _ _ _ n _ _ )                = Just n
        getDeclName (PData _ _ _ _ _ (PDatadecl n _ _ _)) = Just n
        getDeclName _ = Nothing

-- | Checks that an operator name also has a fixity declaration
checkNameFixity :: Name -> IdrisParser ()
checkNameFixity n = do fOk <- fixityOk n
                       unless fOk . fail $
                         "Missing fixity declaration for " ++ show n
      where fixityOk (NS n' _) = fixityOk n'
            fixityOk (UN n') | all (flip elem opChars) (str n') =
                                 do fixities <- fmap idris_infixes get
                                    return . elem (str n') . map (\ (Fix _ op) -> op) $ fixities
                             | otherwise = return True
            fixityOk _ = return True

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

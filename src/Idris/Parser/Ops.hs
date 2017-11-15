{-|
Module      : Idris.Parser.Ops
Description : Parser for operators and fixity declarations.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts, GeneralizedNewtypeDeriving,
             PatternGuards #-}
module Idris.Parser.Ops where

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.Parser.Helpers

import Prelude hiding (pi)

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Char (isAlpha)
import Data.List
import Data.List.NonEmpty (fromList)
import Text.Megaparsec ((<?>))
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Expr as P

-- | Creates table for fixity declarations to build expression parser
-- using pre-build and user-defined operator/fixity declarations
table :: [FixDecl] -> [[P.Operator IdrisParser PTerm]]
table fixes
   = [[prefix "-" (\fc x -> PApp fc (PRef fc [fc] (sUN "negate")) [pexp x])]] ++
      toTable (reverse fixes) ++
     [[noFixityBacktickOperator],
      [binary "$" P.InfixR $ \fc _ x y -> flatten $ PApp fc x [pexp y]],
      [binary "=" P.InfixL $ \fc _ x y -> PApp fc (PRef fc [fc] eqTy) [pexp x, pexp y]],
      [noFixityOperator]]
  where
    flatten                            :: PTerm -> PTerm -- flatten application
    flatten (PApp fc (PApp _ f as) bs) = flatten (PApp fc f (as ++ bs))
    flatten t                          = t

    noFixityBacktickOperator :: P.Operator IdrisParser PTerm
    noFixityBacktickOperator = P.InfixN $ do
                                 (n, fc) <- backtickOperator
                                 return $ \x y -> PApp fc (PRef fc [fc] n) [pexp x, pexp y]

    -- | Operator without fixity (throws an error)
    noFixityOperator :: P.Operator IdrisParser PTerm
    noFixityOperator = P.InfixN $ do
                         indentGt
                         op <- P.try symbolicOperator
                         P.unexpected . P.Label . fromList $ "Operator without known fixity: " ++ op

    -- | Calculates table for fixity declarations
    toTable    :: [FixDecl] -> [[P.Operator IdrisParser PTerm]]
    toTable fs = map (map toBin) (groupBy (\ (Fix x _) (Fix y _) -> prec x == prec y) fs)

    toBin (Fix (PrefixN _) op) = prefix op $ \fc x ->
                                   PApp fc (PRef fc [] (sUN op)) [pexp x]
    toBin (Fix f op)           = binary op (assoc f) $ \fc n x y ->
                                   PApp fc (PRef fc [] n) [pexp x,pexp y]

    assoc (Infixl _) = P.InfixL
    assoc (Infixr _) = P.InfixR
    assoc (InfixN _) = P.InfixN

    isBacktick         :: String -> Bool
    isBacktick (c : _) = c == '_' || isAlpha c
    isBacktick _       = False

    binary :: String -> (IdrisParser (PTerm -> PTerm -> PTerm) -> P.Operator IdrisParser PTerm) -> (FC -> Name -> PTerm -> PTerm -> PTerm) -> P.Operator IdrisParser PTerm
    binary name ctor f
      | isBacktick name = ctor $ P.try $ do
                            (n, fc) <- backtickOperator
                            guard $ show (nsroot n) == name
                            return $ f fc n
      | otherwise       = ctor $ do
                            indentGt
                            fc <- execWriterT $ reservedOp name
                            indentGt
                            return $ f fc (sUN name)

    prefix :: String -> (FC -> PTerm -> PTerm) -> P.Operator IdrisParser PTerm
    prefix name f = P.Prefix $ do
                      fc <- execWriterT $ reservedOp name
                      indentGt
                      return (f fc)

{- | Parses a function used as an operator -- enclosed in backticks

@
  BacktickOperator ::=
    '`' Name '`'
    ;
@
-}
backtickOperator :: IdrisParser (Name, FC)
backtickOperator = P.between (indentGt *> lchar '`') (indentGt *> lchar '`') name

{- | Parses an operator name (either a symbolic name or a backtick-quoted name)

@
  OperatorName ::=
      SymbolicOperator
    | BacktickOperator
    ;
@
-}
operatorName :: IdrisParser (Name, FC)
operatorName =     runWriterT (sUN <$> symbolicOperator)
               <|> backtickOperator

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
operatorFront = runWriterT $ do     P.try $ lchar '(' *> (eqTy <$ reservedOp "=") <* lchar ')'
                                <|> maybeWithNS (lchar '(' *> symbolicOperator <* lchar ')') []

{- | Parses a function (either normal name or operator)

@
  FnName ::= Name | OperatorFront;
@
-}
fnName :: IdrisParser (Name, FC)
fnName = P.try operatorFront <|> name <?> "function name"

{- | Parses a fixity declaration
@
Fixity ::=
  FixityType Natural_t OperatorList Terminator
  ;
@
-}
fixity :: IdrisParser PDecl
fixity = do pushIndent
            f <- fixityType; i <- fst <$> runWriterT natural
            ops <- P.sepBy1 (show . nsroot . fst <$> operatorName) (lchar ',')
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
  where
    alreadyDeclared :: [FixDecl] -> FixDecl -> (FixDecl, [FixDecl])
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

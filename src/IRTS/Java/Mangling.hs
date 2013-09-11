{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module IRTS.Java.Mangling where

import           Core.TT
import           IRTS.Lang
import           IRTS.Simplified

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Error
import           Data.Char

import           Language.Java.Parser
import           Language.Java.Pretty
import           Language.Java.Syntax hiding (Name)
import qualified Language.Java.Syntax as J

import           System.FilePath

prefixCallNamespaces :: Ident -> SDecl -> SDecl
prefixCallNamespaces name (SFun fname args i e) =
  SFun fname args i (prefixCallNamespacesExp name e)
  where
    prefixCallNamespacesExp :: Ident -> SExp -> SExp
    prefixCallNamespacesExp (Ident name) (SApp tail (NS n ns) args) =
      SApp tail (NS n (name:ns)) args
    prefixCallNamespacesExp name (SLet var e1 e2) =
      SLet var (prefixCallNamespacesExp name e1) (prefixCallNamespacesExp name e2)
    prefixCallNamespacesExp name (SUpdate var e) =
      SUpdate var (prefixCallNamespacesExp name e)
    prefixCallNamespacesExp name (SCase var alts) =
      SCase var (map (prefixCallNamespacesCase name) alts)
    prefixCallNamespacesExp name (SChkCase var alts) =
      SChkCase var (map (prefixCallNamespacesCase name) alts)
    prefixCallNamespacesExp _ exp = exp

    prefixCallNamespacesCase :: Ident -> SAlt -> SAlt
    prefixCallNamespacesCase name (SConCase x y n ns e) =
      SConCase x y n ns (prefixCallNamespacesExp name e)
    prefixCallNamespacesCase name (SConstCase c e) =
      SConstCase c (prefixCallNamespacesExp name e)
    prefixCallNamespacesCase name (SDefaultCase e) =
      SDefaultCase (prefixCallNamespacesExp name e)

liftParsed :: (Show e, MonadError String m) => Either e a -> m a
liftParsed = either (\ err -> throwError $ "Parser error: " ++ (show err))
                    (return)

mkClassName :: (MonadError String m) => FilePath -> m Ident
mkClassName path =
  liftParsed . parser ident . takeBaseName $ takeFileName path

mangleWithPrefix :: (Applicative m, MonadError String m) => String -> Name -> m Ident
mangleWithPrefix prefix (NS name _) = mangleWithPrefix prefix name
mangleWithPrefix prefix (MN i name) =
  (\ (Ident x) -> Ident $ x ++ ('_' : show i))
  <$> mangleWithPrefix prefix (UN name)
mangleWithPrefix prefix (UN name) =
  liftParsed
  . parser ident
  . (prefix ++)
  . cleanNonLetter
  $ cleanWs False name
  where
    cleanNonLetter (x:xs)
      | x == '#' = "_Hash" ++ cleanNonLetter xs
      | x == '@' = "_At" ++ cleanNonLetter xs
      | x == '$' = "_Dollar" ++ cleanNonLetter xs
      | x == '!' = "_Bang" ++ cleanNonLetter xs
      | x == '.' = "_Dot" ++ cleanNonLetter xs
      | x == '\'' = "_Prime" ++ cleanNonLetter xs
      | x == '*' = "_Times" ++ cleanNonLetter xs
      | x == '+' = "_Plus" ++ cleanNonLetter xs
      | x == '/' = "_Divide" ++ cleanNonLetter xs
      | x == '-' = "_Minus" ++ cleanNonLetter xs
      | x == '%' = "_Mod" ++ cleanNonLetter xs
      | x == '<' = "_LessThan" ++ cleanNonLetter xs
      | x == '=' = "_Equals" ++ cleanNonLetter xs
      | x == '>' = "_MoreThan" ++ cleanNonLetter xs
      | x == '[' = "_LSBrace" ++ cleanNonLetter xs
      | x == ']' = "_RSBrace" ++ cleanNonLetter xs
      | x == '(' = "_LBrace" ++ cleanNonLetter xs
      | x == ')' = "_RBrace" ++ cleanNonLetter xs
      | x == '_' = "__" ++ cleanNonLetter xs
      | not (isAlphaNum x) = "_" ++ (show $ ord x) ++ xs
      | otherwise = x:cleanNonLetter xs
    cleanNonLetter [] = []
    cleanWs capitalize (x:xs)
      | isSpace x  = cleanWs True xs
      | capitalize = (toUpper x) : (cleanWs False xs)
      | otherwise  = x : (cleanWs False xs)
    cleanWs _ [] = []
mangleWithPrefix prefix s@(SN _) = mangleWithPrefix prefix (UN (showCG s))

mangle :: (Applicative m, MonadError String m) => Name -> m Ident
mangle = mangleWithPrefix "__IDRCG__"

mangle' :: Name -> Ident
mangle' = either error id . mangleWithPrefix "__IDRCG__"

mangleFull :: (Applicative m, MonadError String m) => Name -> m J.Name
mangleFull (NS name (rootns:nss)) =
  (\ r n ns -> J.Name (r:(ns ++ [n])))
  <$> mangleWithPrefix "" (UN rootns)
  <*> mangle name
  <*> mapM (mangle . UN) nss
mangleFull n = J.Name . (:[]) <$> mangle n

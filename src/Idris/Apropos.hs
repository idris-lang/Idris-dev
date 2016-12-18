{-|
Module      : Idris.Apropos
Description : Search loaded Idris code and named modules for things.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Apropos (apropos, aproposModules) where

import Idris.AbsSyntax
import Idris.Core.Evaluate (Def(..), ctxtAlist)
import Idris.Core.TT (Binder(..), Const(..), Name(..), NameType(..), TT(..),
                      Type, lookupCtxtExact, toAlist)
import Idris.Docstrings (DocTerm, Docstring, containsText)

import Data.List (intersperse, nub, nubBy)
import qualified Data.Text as T

-- | Find definitions that are relevant to all space-delimited components of
-- some string. Relevance is one or more of the following:
--
-- * the string is a substring of the name
--
-- * the string occurs in the documentation string
--
-- * the type of the definition is apropos
apropos :: IState -> T.Text -> [Name]
apropos ist what = let defs = ctxtAlist (tt_ctxt ist)
                       docs = toAlist (idris_docstrings ist)
                   in nub (map fst (isAproposAll parts defs) ++
                           map fst (isAproposAll parts docs))
  where isAproposAll []          xs = xs
        isAproposAll (what:more) xs = filter (isApropos what)
                                             (isAproposAll more xs)
        parts = filter ((> 0) . T.length) . T.splitOn (T.pack " ") $ what

-- | Find modules whose names or docstrings contain all the
-- space-delimited components of some string.
aproposModules :: IState -> T.Text -> [(String, Docstring DocTerm)]
aproposModules ist what = let mods  = toAlist (idris_moduledocs ist)
                              found = nubBy (\x y -> fst x == fst y)
                                            (isAproposAll parts mods)
                          in map unModName found
  where isAproposAll []          xs = xs
        isAproposAll (what:more) xs = filter (\(n,d) -> isApropos what n || isApropos what d)
                                             (isAproposAll more xs)
        parts = filter ((> 0) . T.length) . T.splitOn (T.pack " ") $ what
        unModName (NS _ ns, d) = ((concat . intersperse "." . map T.unpack . reverse) ns, d)
        unModName (n,       d) = ("<<MODULE>>", d)

textIn :: T.Text -> T.Text -> Bool
textIn a b = T.isInfixOf (T.toLower a) (T.toLower b)

class Apropos a where
  isApropos :: T.Text -> a -> Bool

instance Apropos Name where
  isApropos str (UN n)     = textIn str n
  isApropos str (NS n' ns) = isApropos str n' || any (textIn str) ns
  -- Handle special names from stdlib
  isApropos str n | (n == unitTy || n == unitCon) && str == T.pack "()" = True
                  | (n == pairTy || n == pairCon) && str == T.pack "," = True
                  | n == eqTy && str == T.pack "=" = True
                  | n == eqCon && (T.toLower str) == T.pack "Refl" = True
                  | (n == sigmaTy || n == sigmaCon) && str == T.pack "**" = True
  isApropos _   _          = False -- we don't care about case blocks, MNs, etc

instance Apropos Def where
  isApropos str (Function ty tm) = isApropos str ty
  isApropos str (TyDecl _ ty) = isApropos str ty
  isApropos str (Operator ty _ _) = isApropos str ty
  isApropos str (CaseOp _ ty ty' _ _ _) = isApropos str ty

instance Apropos (Binder (TT Name)) where
  isApropos str (Lam _ ty)    = str == T.pack "\\" || isApropos str ty
  isApropos str (Pi _ _ ty _) = str == T.pack "->" || isApropos str ty
  isApropos str (Let ty val)  = str == T.pack "let" || isApropos str ty || isApropos str val
  isApropos str (NLet ty val) = str == T.pack "let" || isApropos str ty || isApropos str val
  isApropos str _             = False -- these shouldn't occur in defined libraries

instance Apropos (TT Name) where
  isApropos str (P Ref n ty) = isApropos str n || isApropos str ty
  isApropos str (P (TCon _ _) n ty) = isApropos str n || isApropos str ty
  isApropos str (P (DCon _ _ _) n ty) = isApropos str n || isApropos str ty
  isApropos str (P Bound _ ty)      = isApropos str ty
  isApropos str (Bind n b tm)       = isApropos str b || isApropos str tm
  isApropos str (App _ t1 t2)       = isApropos str t1 || isApropos str t2
  isApropos str (Constant const)    = isApropos str const
  isApropos str _                   = False

instance Apropos Const where
  isApropos str c = textIn str (T.pack (show c))

instance Apropos (Docstring a) where
  isApropos str d = containsText str d

instance (Apropos a, Apropos b) => Apropos (a, b) where
  isApropos str (x, y) = isApropos str x || isApropos str y

instance (Apropos a) => Apropos (Maybe a) where
  isApropos str (Just x) = isApropos str x
  isApropos _   Nothing  = False

instance (Apropos a) => Apropos [a] where
  isApropos str xs = any (isApropos str) xs

defType :: Def -> Type
defType (Function t _) = t
defType (TyDecl _ t) = t
defType (Operator t _ _) = t
defType (CaseOp _ t _ _ _ _) = t

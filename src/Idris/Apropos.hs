module Idris.Apropos where

import Idris.AbsSyntax
import Idris.Core.Evaluate (ctxtAlist, Def(..))
import Idris.Core.TT (Name(..), Type, TT(..), NameType(..), Binder(..), Const(..),
                      lookupCtxtExact, toAlist)
import Idris.Docstrings (Docstring, containsText)

import Data.List (nub)
import qualified Data.Text as T

-- | Find definitions that are relevant to some string. Relevance is one or
-- more of the following:
--
-- * the string is a substring of the name
--
-- * the string occurs in the documentation string
--
-- * the type of the definition is apropos
apropos :: IState -> T.Text -> [Name]
apropos ist what = let defs = ctxtAlist (tt_ctxt ist)
                       docs = toAlist (idris_docstrings ist)
                   in nub (map fst (filter (isApropos what) defs) ++
                           map fst (filter (isApropos what) docs))

class Apropos a where
  isApropos :: T.Text -> a -> Bool

instance Apropos Name where
  isApropos str (UN n)     = T.isInfixOf str n
  isApropos str (NS n' ns) = isApropos str n' || any (T.isInfixOf str) ns
  -- Handle special names from stdlib
  isApropos str n | (n == unitTy || n == unitCon) && str == T.pack "()" = True
                  | n == falseTy && str == T.pack "_|_" = True
                  | (n == pairTy || n == pairCon) && str == T.pack "," = True
                  | n == eqTy && str == T.pack "=" = True
                  | n == eqCon && str == T.pack "refl" = True
                  | (n == sigmaTy || n == existsCon) && str == T.pack "**" = True
  isApropos _   _          = False -- we don't care about case blocks, MNs, etc

instance Apropos Def where
  isApropos str (Function ty tm) = isApropos str ty
  isApropos str (TyDecl _ ty) = isApropos str ty
  isApropos str (Operator ty _ _) = isApropos str ty
  isApropos str (CaseOp _ ty ty' _ _ _) = isApropos str ty

instance Apropos (Binder (TT Name)) where
  isApropos str (Lam ty)      = isApropos str ty
  isApropos str (Pi ty)       = isApropos str ty
  isApropos str (Let ty val)  = isApropos str ty || isApropos str val
  isApropos str (NLet ty val) = isApropos str ty || isApropos str val
  isApropos str _             = False -- these shouldn't occur in defined libraries

instance Apropos (TT Name) where
  isApropos str (P Ref n ty) = isApropos str n || isApropos str ty
  isApropos str (P (TCon _ _) n ty) = isApropos str n || isApropos str ty
  isApropos str (P (DCon _ _) n ty) = isApropos str n || isApropos str ty
  isApropos str (P Bound _ ty)      = isApropos str ty
  isApropos str (Bind n b tm)       = isApropos str b || isApropos str tm
  isApropos str (App t1 t2)         = isApropos str t1 || isApropos str t2
  isApropos str (Constant const)    = isApropos str const
  isApropos str _                   = False

instance Apropos Const where
  isApropos str c = T.isInfixOf str (T.pack (show c))

instance Apropos Docstring where
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

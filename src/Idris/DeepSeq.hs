{-|
Module      : Idris.DeepSeq
Description : NFData instances for Idris' types
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Idris.DeepSeq(
    module Idris.DeepSeq
  , module Idris.Core.DeepSeq
  ) where

import Idris.AbsSyntaxTree
import Idris.Colours
import Idris.Core.DeepSeq
import Idris.Core.TT
import Idris.Docstrings
import qualified Idris.Docstrings as D
import IRTS.CodegenCommon (OutputType(..))
import IRTS.Lang (PrimFn(..))

import Util.DynamicLinker

import qualified Cheapskate.Types as CT
import Control.DeepSeq
import Network.Socket (PortNumber)

-- These types don't have Generic instances
instance NFData CT.Options where
  rnf (CT.Options x1 x2 x3 x4) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()

instance NFData CT.ListType where
  rnf (CT.Bullet c) = rnf c `seq` ()
  rnf (CT.Numbered nw i) = rnf nw `seq` rnf i `seq` ()

instance NFData CT.CodeAttr where
  rnf (CT.CodeAttr a b) = rnf a `seq` rnf b `seq` ()

instance NFData CT.NumWrapper where
  rnf CT.PeriodFollowing = ()
  rnf CT.ParenFollowing = ()

instance NFData DynamicLib where
    rnf (Lib x _) = rnf x `seq` ()

instance NFData IdrisColour where
  rnf (IdrisColour _ x2 x3 x4 x5) = rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()

instance NFData PortNumber where
  rnf x = rnf $ show x

-- Handle doesn't have an NFData instance
instance NFData OutputMode where
  rnf (RawOutput x) = ()
  rnf (IdeMode x y) = rnf x `seq` ()

instance NFData a => NFData (D.Docstring a)
instance NFData ConsoleWidth
instance NFData PrimFn
instance NFData SyntaxRules
instance NFData Opt
instance NFData REPLPort
instance NFData TIData
instance NFData IOption
instance NFData LanguageExt
instance NFData Optimisation
instance NFData ColourTheme
instance NFData OutputType
instance NFData IBCWrite
instance NFData a => NFData (D.Block a)
instance NFData a => NFData (D.Inline a)
instance NFData DocTerm
instance NFData SizeChange
instance NFData FnInfo
instance NFData Codegen
instance NFData IRFormat
instance NFData LogCat
instance NFData CGInfo
instance NFData Fixity
instance NFData FixDecl
instance NFData Static
instance NFData ArgOpt
instance NFData Plicity
instance NFData FnOpt
instance NFData DataOpt
instance NFData Directive
instance (NFData t) => NFData (PDecl' t)
instance NFData t => NFData (ProvideWhat' t)
instance NFData PunInfo
instance (NFData t) => NFData (PClause' t)
instance (NFData t) => NFData (PData' t)
instance NFData PTerm
instance NFData PAltType
instance (NFData t) => NFData (PTactic' t)
instance (NFData t) => NFData (PDo' t)
instance (NFData t) => NFData (PArg' t)
instance NFData InterfaceInfo
instance NFData RecordInfo
instance NFData OptInfo
instance NFData TypeInfo
instance (NFData t) => NFData (DSL' t)
instance NFData SynContext
instance NFData Syntax
instance NFData SSymbol
instance NFData Using
instance NFData SyntaxInfo
instance NFData DefaultTotality
instance NFData IState
instance NFData InteractiveOpts

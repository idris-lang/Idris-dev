{-|
Module      : Idris.Core.DeepSeq
Description : NFData instances for TT.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE BangPatterns, ViewPatterns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Idris.Core.DeepSeq where

import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT

import Control.DeepSeq

instance NFData Name

instance NFData Context

-- | Forcing the contents of a context, for diagnosing and working
-- around space leaks
forceDefCtxt :: Context -> Context
forceDefCtxt (force -> !ctxt) = ctxt

instance NFData NameOutput
instance NFData TextFormatting
instance NFData Ordering
instance NFData OutputAnnotation
instance NFData SpecialName
instance NFData Universe
instance NFData Raw
instance NFData FC
instance NFData FC'
instance NFData Provenance
instance NFData UConstraint
instance NFData ConstraintFC
instance NFData Err
instance NFData ErrorReportPart
instance NFData ImplicitInfo
instance NFData RigCount
instance (NFData b) => NFData (Binder b)
instance NFData UExp
instance NFData NameType
instance NFData NativeTy
instance NFData IntTy
instance NFData ArithTy
instance NFData Const
instance (NFData a) => NFData (AppStatus a)
instance (NFData n) => NFData (TT n)
instance NFData Accessibility
instance NFData Totality
instance NFData PReason
instance NFData MetaInformation
instance NFData Def
instance NFData CaseInfo
instance NFData CaseDefs
instance NFData CaseType
instance (NFData t) => NFData (SC' t)
instance (NFData t) => NFData (CaseAlt' t)

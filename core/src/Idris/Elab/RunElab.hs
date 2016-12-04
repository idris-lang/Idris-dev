{-|
Module      : Idris.Elab.RunElab
Description : Code to run the elaborator process.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Elab.RunElab (elabRunElab) where

import Idris.AbsSyntax
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Elab.Term
import Idris.Elab.Value (elabVal)
import Idris.Error
import Idris.Output (iWarn, iputStrLn, pshow, sendHighlighting)

elabScriptTy :: Type
elabScriptTy = App Complete (P Ref (sNS (sUN "Elab") ["Elab", "Reflection", "Language"]) Erased)
                   (P Ref unitTy Erased)

mustBeElabScript :: Type -> Idris ()
mustBeElabScript ty =
    do ctxt <- getContext
       case converts ctxt [] ty elabScriptTy of
            OK _    -> return ()
            Error e -> ierror e

elabRunElab :: ElabInfo -> FC -> PTerm -> [String] -> Idris ()
elabRunElab info fc script' ns =
  do -- First elaborate the script itself
     (script, scriptTy) <- elabVal info ERHS script'
     mustBeElabScript scriptTy
     ist <- getIState
     ctxt <- getContext
     (ElabResult tyT' defer is ctxt' newDecls highlights newGName, log) <-
        tclift $ elaborate (constraintNS info) ctxt (idris_datatypes ist) (idris_name ist) (sMN 0 "toplLevelElab") elabScriptTy initEState
                 (transformErr RunningElabScript
                   (erun fc (do tm <- runElabAction info ist fc [] script ns
                                EState is _ impls highlights _ _ <- getAux
                                ctxt <- get_context
                                let ds = [] -- todo
                                log <- getLog
                                newGName <- get_global_nextname
                                return (ElabResult tm ds (map snd is) ctxt impls highlights newGName))))



     setContext ctxt'
     processTacticDecls info newDecls
     sendHighlighting highlights
     updateIState $ \i -> i { idris_name = newGName }

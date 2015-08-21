module Idris.Elab.RunElab (elabRunElab) where

import Idris.Elab.Term
import Idris.Elab.Value (elabVal)

import Idris.AbsSyntax
import Idris.Error

import Idris.Core.Elaborate hiding (Tactic (..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.TT
import Idris.Core.Typecheck

import Idris.Output (iputStrLn, pshow, iWarn, sendHighlighting)

elabScriptTy :: Type
elabScriptTy = App Complete (P Ref (sNS (sUN "Elab") ["Elab", "Reflection", "Language"]) Erased)
                   (P Ref unitTy Erased)

mustBeElabScript :: Type -> Idris ()
mustBeElabScript ty =
    do ctxt <- getContext
       case converts ctxt [] ty elabScriptTy of
            OK _    -> return ()
            Error e -> ierror e

elabRunElab :: ElabInfo -> FC -> PTerm -> Idris ()
elabRunElab info fc script' =
  do -- First elaborate the script itself
     (script, scriptTy) <- elabVal info ERHS script'
     mustBeElabScript scriptTy
     ist <- getIState
     ctxt <- getContext
     (ElabResult tyT' defer is ctxt' newDecls highlights, log) <-
        tclift $ elaborate ctxt (idris_datatypes ist) (sMN 0 "toplLevelElab") elabScriptTy initEState
                 (transformErr RunningElabScript
                   (erun fc (do tm <- runElabAction ist fc [] script [] --TODO namespace from parser
                                EState is _ impls highlights <- getAux
                                ctxt <- get_context
                                let ds = [] -- todo
                                log <- getLog
                                return (ElabResult tm ds (map snd is) ctxt impls highlights))))



     setContext ctxt'
     processTacticDecls info newDecls
     sendHighlighting highlights

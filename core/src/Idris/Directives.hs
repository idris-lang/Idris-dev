{-|
Module      : Idris.Directives
Description : Act upon Idris directives.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Directives(directiveAction) where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Imports
import Idris.Output (sendHighlighting)

import Util.DynamicLinker

-- | Run the action corresponding to a directive
directiveAction :: Directive -> Idris ()
directiveAction (DLib cgn lib) = do
  addLib cgn lib
  addIBC (IBCLib cgn lib)

directiveAction (DLink cgn obj) = do
  dirs <- allImportDirs
  o <- runIO $ findInPath dirs obj
  addIBC (IBCObj cgn obj) -- just name, search on loading ibc
  addObjectFile cgn o

directiveAction (DFlag cgn flag) = do
  let flags = words flag
  mapM_ (\f -> addIBC (IBCCGFlag cgn f)) flags
  mapM_ (addFlag cgn) flags

directiveAction (DInclude cgn hdr) = do
  addHdr cgn hdr
  addIBC (IBCHeader cgn hdr)

directiveAction (DHide n') = do
  ns <- allNamespaces n'
  mapM_ (\n -> do
            setAccessibility n Hidden
            addIBC (IBCAccess n Hidden)) ns
directiveAction (DFreeze n') = do
  ns <- allNamespaces n'
  mapM_ (\n -> do
            setAccessibility n Frozen
            addIBC (IBCAccess n Frozen)) ns
directiveAction (DThaw n') = do
  ns <- allNamespaces n'
  mapM_ (\n -> do
            ctxt <- getContext
            case lookupDefAccExact n False ctxt of
                 Just (_, Frozen) -> do setAccessibility n Public
                                        addIBC (IBCAccess n Public)
                 _ -> throwError (Msg (show n ++ " is not frozen"))) ns
directiveAction (DInjective n') = do
  ns <- allNamespaces n'
  mapM_ (\n -> do
            setInjectivity n True
            addIBC (IBCInjective n True)) ns
directiveAction (DSetTotal n') = do
  ns <- allNamespaces n'
  mapM_ (\n -> do
            setTotality n (Total [])
            addIBC (IBCTotal n (Total []))) ns

directiveAction (DAccess acc) = do updateIState (\i -> i { default_access = acc })

directiveAction (DDefault tot) =  do updateIState (\i -> i { default_total = tot })

directiveAction (DLogging lvl) = setLogLevel (fromInteger lvl)

directiveAction (DDynamicLibs libs) = do
  added <- addDyLib libs
  case added of
    Left lib  -> addIBC (IBCDyLib (lib_name lib))
    Right msg -> fail msg

directiveAction (DNameHint ty tyFC ns) = do
  ty' <- disambiguate ty
  mapM_ (addNameHint ty' . fst) ns
  mapM_ (\n -> addIBC (IBCNameHint (ty', fst n))) ns
  sendHighlighting $ [(tyFC, AnnName ty' Nothing Nothing Nothing)] ++ map (\(n, fc) -> (fc, AnnBoundName n False)) ns

directiveAction (DErrorHandlers fn nfc arg afc ns) = do
  fn' <- disambiguate fn
  ns' <- mapM (\(n, fc) -> do
                  n' <- disambiguate n
                  return (n', fc)) ns
  addFunctionErrorHandlers fn' arg (map fst ns')
  mapM_ (addIBC . IBCFunctionErrorHandler fn' arg . fst) ns'
  sendHighlighting $
       [ (nfc, AnnName fn' Nothing Nothing Nothing)
       , (afc, AnnBoundName arg False)
       ] ++ map (\(n, fc) -> (fc, AnnName n Nothing Nothing Nothing)) ns'

directiveAction (DLanguage ext) = addLangExt ext

directiveAction (DDeprecate n reason) = do
  n' <- disambiguate n
  addDeprecated n' reason
  addIBC (IBCDeprecate n' reason)

directiveAction (DFragile n reason) = do
  n' <- disambiguate n
  addFragile n' reason
  addIBC (IBCFragile n' reason)

directiveAction (DAutoImplicits b) = setAutoImpls b
directiveAction (DUsed fc fn arg)  = addUsedName fc fn arg

disambiguate :: Name -> Idris Name
disambiguate n = do
  i <- getIState
  case lookupCtxtName n (idris_implicits i) of
    [(n', _)] -> return n'
    []        -> throwError (NoSuchVariable n)
    more      -> throwError (CantResolveAlts (map fst more))


allNamespaces :: Name -> Idris [Name]
allNamespaces n = do
  i <- getIState
  case lookupCtxtName n (idris_implicits i) of
    [(n', _)] -> return [n']
    []        -> throwError (NoSuchVariable n)
    more      -> return (map fst more)

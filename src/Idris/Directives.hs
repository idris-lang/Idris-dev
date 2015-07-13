
module Idris.Directives(directiveAction) where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.Imports

import Idris.Core.Evaluate
import Idris.Core.TT

import Util.DynamicLinker

-- | Run the action corresponding to a directive
directiveAction :: Directive -> Idris ()
directiveAction (DLib cgn lib) = do addLib cgn lib
                                    addIBC (IBCLib cgn lib)

directiveAction (DLink cgn obj) = do dirs <- allImportDirs
                                     o <- runIO $ findInPath dirs obj
                                     addIBC (IBCObj cgn obj) -- just name, search on loading ibc
                                     addObjectFile cgn o

directiveAction (DFlag cgn flag) = do addIBC (IBCCGFlag cgn flag)
                                      addFlag cgn flag

directiveAction (DInclude cgn hdr) = do addHdr cgn hdr
                                        addIBC (IBCHeader cgn hdr)

directiveAction (DHide n) = do setAccessibility n Hidden
                               addIBC (IBCAccess n Hidden)

directiveAction (DFreeze n) = do setAccessibility n Frozen
                                 addIBC (IBCAccess n Frozen)

directiveAction (DAccess acc) = do updateIState (\i -> i { default_access = acc })

directiveAction (DDefault tot) =  do updateIState (\i -> i { default_total = tot })

directiveAction (DLogging lvl) = setLogLevel (fromInteger lvl)

directiveAction (DDynamicLibs libs) = do added <- addDyLib libs
                                         case added of
                                             Left lib -> addIBC (IBCDyLib (lib_name lib))
                                             Right msg -> fail $ msg

directiveAction (DNameHint ty ns) = do ty' <- disambiguate ty
                                       mapM_ (addNameHint ty') ns
                                       mapM_ (\n -> addIBC (IBCNameHint (ty', n))) ns

directiveAction (DErrorHandlers fn arg ns) = do fn' <- disambiguate fn
                                                ns' <- mapM disambiguate ns
                                                addFunctionErrorHandlers fn' arg ns'
                                                mapM_ (addIBC .
                                                    IBCFunctionErrorHandler fn' arg) ns'

directiveAction (DLanguage ext) = addLangExt ext

directiveAction (DUsed fc fn arg) = addUsedName fc fn arg

disambiguate :: Name -> Idris Name
disambiguate n = do i <- getIState
                    case lookupCtxtName n (idris_implicits i) of
                              [(n', _)] -> return n'
                              []        -> throwError (NoSuchVariable n)
                              more      -> throwError (CantResolveAlts (map fst more))

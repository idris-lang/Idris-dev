{-|
Module      : Idris.Elab.Data
Description : Code to elaborate data structures.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE CPP, PatternGuards #-}
module Idris.Elab.Data(elabData) where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Delaborate
import Idris.Docstrings
import Idris.Elab.Rewrite
import Idris.Elab.Type
import Idris.Elab.Utils
import Idris.Elab.Value
import Idris.Error
import Idris.Output (iWarn, sendHighlighting)

import Util.Pretty

#if (MIN_VERSION_base(4,11,0))
import Prelude hiding (id, (.), (<>))
#else
import Prelude hiding (id, (.))
#endif

import Control.Category
import Control.Monad
import Control.Monad.State.Strict as State
import Data.Char (isLetter, toLower)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T

warnLC :: FC -> Name -> Idris ()
warnLC fc n
   = iWarn fc $ annName n <+> text "has a name which may be implicitly bound."
           <> line <> text "This is likely to lead to problems!"

elabData :: ElabInfo -> SyntaxInfo -> Docstring (Either Err PTerm)-> [(Name, Docstring (Either Err PTerm))] -> FC -> DataOpts -> PData -> Idris ()
elabData info syn doc argDocs fc opts (PLaterdecl n nfc t_in)
    = do logElab 1 (show (fc, doc))
         checkUndefined fc n
         when (implicitable (nsroot n)) $ warnLC fc n
         (cty, _, t, inacc) <- buildType info syn fc [] n t_in

         addIBC (IBCDef n)
         updateContext (addTyDecl n (TCon 0 0) cty) -- temporary, to check cons
         sendHighlighting $ S.fromList [(FC' nfc, AnnName n Nothing Nothing Nothing)]

elabData info syn doc argDocs fc opts (PDatadecl n nfc t_in dcons)
    = do let codata = Codata `elem` opts
         logElab 1 (show fc)
         undef <- isUndefined fc n
         when (implicitable (nsroot n)) $ warnLC fc n
         (cty, ckind, t, inacc) <- buildType info syn fc [] n t_in
         -- if n is defined already, make sure it is just a type declaration
         -- with the same type we've just elaborated, and no constructors
         -- yet
         i <- getIState
         checkDefinedAs fc n cty i
         -- temporary, to check cons
         when undef $ updateContext (addTyDecl n (TCon 0 0) cty)
         let cnameinfo = cinfo info (map cname dcons)
         unique <- case getRetTy (normalise (tt_ctxt i) [] cty) of
                        UType UniqueType -> return True
                        UType _ -> return False
                        TType _ -> return False
                        rt -> tclift $ tfail (At fc (Elaborating "type constructor " n Nothing (Msg "Not a valid type constructor")))
         cons <- mapM (elabCon cnameinfo syn n codata (getRetTy cty) ckind) dcons
         ttag <- getName

         ctxt <- getContext
         let params = findParams n (normalise ctxt [] cty) (map snd cons)

         logElab 2 $ "Parameters : " ++ show params
         addParamConstraints fc params cty cons

         i <- getIState
         -- TI contains information about mutually declared types - this will
         -- be updated when the mutual block is complete
         putIState (i { idris_datatypes =
                          addDef n (TI (map fst cons) codata opts params [n]
                                             (any linearArg (map snd cons)))
                                             (idris_datatypes i) })
         addIBC (IBCDef n)
         addIBC (IBCData n)
         checkDocs fc argDocs t
         doc' <- elabDocTerms info doc
         argDocs' <- mapM (\(n, d) -> do d' <- elabDocTerms info d
                                         return (n, d')) argDocs
         addDocStr n doc' argDocs'
         addIBC (IBCDoc n)
         let metainf = DataMI params
         addIBC (IBCMetaInformation n metainf)
         -- TMP HACK! Make this a data option
         updateContext (addDatatype (Data n ttag cty unique cons))
         updateContext (setMetaInformation n metainf)

         mapM_ totcheck (zip (repeat fc) (map fst cons))
--          mapM_ (checkPositive n) cons

         -- if there's exactly one constructor,
         -- mark both the type and the constructor as detaggable
         case cons of
            [(cn,ct)] -> setDetaggable cn >> setDetaggable n
                >> addIBC (IBCOpt cn) >> addIBC (IBCOpt n)
            _ -> return ()

         -- create a rewriting lemma
         when (n /= sUN "=") $
            elabRewriteLemma info n cty
         -- Emit highlighting info
         sendHighlighting $ S.fromList $ [(FC' nfc, AnnName n Nothing Nothing Nothing)] ++
           map (\(_, _, n, nfc, _, _, _) ->
                 (FC' nfc, AnnName n Nothing Nothing Nothing))
               dcons
  where
        checkDefinedAs fc n t i
            = let defined = tclift $ tfail (At fc (AlreadyDefined n))
                  ctxt = tt_ctxt i in
                case lookupDef n ctxt of
                   [] -> return ()
                   [TyDecl _ ty] ->
                      case converts ctxt [] t ty of
                           OK () -> case lookupCtxtExact n (idris_datatypes i) of
                                         Nothing -> return ()
                                         _ -> defined
                           _ -> defined
                   _ -> defined


        cname (_, _, n, _, _, _, _) = n

        -- Abuse of ElabInfo.
        -- TODO Contemplate whether the ElabInfo type needs modification.
        cinfo :: ElabInfo -> [Name] -> ElabInfo
        cinfo info ds
          = let newps = params info
                dsParams = map (\n -> (n, [])) ds
                newb = addAlist dsParams (inblock info) in
                info { params = newps,
                       inblock = newb,
                       liftname = id -- Is this appropriate?
                     }

elabCon :: ElabInfo -> SyntaxInfo -> Name -> Bool ->
           Type -> -- for unique kind checking
           Type -> -- data type's kind
           (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, FC, PTerm, FC, [Name]) ->
           Idris (Name, Type)
elabCon info syn tn codata expkind dkind (doc, argDocs, n, nfc, t_in, fc, forcenames)
    = do checkUndefined fc n
         when (implicitable (nsroot n)) $ warnLC fc n
         logElab 2 $ show fc ++ ":Constructor " ++ show n ++ " : " ++ show t_in
         (cty, ckind, t, inacc) <- buildType info syn fc [Constructor] n (if codata then mkLazy t_in else t_in)
         ctxt <- getContext
         let cty' = normalise ctxt [] cty
         checkUniqueKind ckind expkind

         -- Check that the constructor type is, in fact, a part of the family being defined
         tyIs n cty'
         -- Need to calculate forceability from the non-normalised type,
         -- because we might not be able to export the definitions which
         -- we're normalising which changes the forceability status!
         let force = if tn == sUN "Delayed"
                        then [] -- TMP HACK! Totality checker needs this info
                        else forceArgs ctxt tn cty

         logElab 5 $ show fc ++ ":Constructor " ++ show n ++ " elaborated : " ++ show t
         logElab 5 $ "Inaccessible args: " ++ show inacc
         logElab 5 $ "Forceable args: " ++ show force
         logElab 2 $ "---> " ++ show n ++ " : " ++ show cty

         -- Add to the context (this is temporary, so that later constructors
         -- can be indexed by it)
         updateContext (addTyDecl n (DCon 0 0 False) cty)

         addIBC (IBCDef n)
         checkDocs fc argDocs t
         doc' <- elabDocTerms info doc
         argDocs' <- mapM (\(n, d) -> do d' <- elabDocTerms info d
                                         return (n, d')) argDocs
         addDocStr n doc' argDocs'
         addIBC (IBCDoc n)
         fputState (opt_inaccessible . ist_optimisation n) inacc
         fputState (opt_forceable . ist_optimisation n) force
         addIBC (IBCOpt n)
         return (n, cty)
  where
    tyIs con (Bind n b sc) = tyIs con (substV (P Bound n Erased) sc)
    tyIs con t | (P Bound n' _, _) <- unApply t
        = if n' /= tn then
               tclift $ tfail (At fc (Elaborating "constructor " con Nothing
                         (Msg ("Type level variable " ++ show n' ++ " is not " ++ show tn))))
             else return ()
    tyIs con t | (P _ n' _, _) <- unApply t
        = if n' /= tn then tclift $ tfail (At fc (Elaborating "constructor " con Nothing (Msg (show n' ++ " is not " ++ show tn))))
             else return ()
    tyIs con t = tclift $ tfail (At fc (Elaborating "constructor " con Nothing (Msg (show t ++ " is not " ++ show tn))))

    mkLazy (PPi pl n nfc ty sc)
        = let ty' = if getTyName ty
                       then PApp fc (PRef fc [] (sUN "Delayed"))
                            [pexp (PRef fc [] (sUN "Infinite")),
                             pexp ty]
                       else ty in
              PPi pl n nfc ty' (mkLazy sc)
    mkLazy t = t

    getTyName (PApp _ (PRef _ _ n) _) = n == nsroot tn
    getTyName (PRef _ _ n) = n == nsroot tn
    getTyName _ = False

    -- if the constructor is a UniqueType, the datatype must be too
    -- (AnyType is fine, since that is checked for uniqueness too)
    -- if hte contructor is AnyType, the datatype must be at least AnyType
    checkUniqueKind (UType NullType) (UType NullType) = return ()
    checkUniqueKind (UType NullType) _
        = tclift $ tfail (At fc (UniqueKindError NullType n))
    checkUniqueKind (UType UniqueType) (UType UniqueType) = return ()
    checkUniqueKind (UType UniqueType) (UType AllTypes) = return ()
    checkUniqueKind (UType UniqueType) _
        = tclift $ tfail (At fc (UniqueKindError UniqueType n))
    checkUniqueKind (UType AllTypes) (UType AllTypes) = return ()
    checkUniqueKind (UType AllTypes) (UType UniqueType) = return ()
    checkUniqueKind (UType AllTypes) _
        = tclift $ tfail (At fc (UniqueKindError AllTypes n))
    checkUniqueKind _ _ = return ()

forceArgs :: Context -> Name -> Type -> [Int]
forceArgs ctxt tn ty = forceFrom 0 ty
  where
    -- for each argument, substitute in MN pos "FF"
    -- then when we look at the return type, if we see MN pos name
    -- constructor guarded, then 'pos' is a forceable position
    forceFrom :: Int -> Type -> [Int]
    forceFrom i (Bind n (Pi _ _ _ _) sc)
       = forceFrom (i + 1) (substV (P Ref (sMN i "FF") Erased) sc)
    forceFrom i sc
        -- Go under the top level type application
        -- We risk affecting erasure of more complex indices, so we'll only
        -- mark something forced if *everything* which appears in an index
        -- is forceable
        -- (FIXME: Actually the real risk is if we erase something a programmer
        -- definitely wants, which is particularly the case with 'views'.
        -- So perhaps we need a way of marking that in the source?)
        | (P _ ty _, args) <- unApply sc,
          ty == tn -- Must be the right top level type!
             = if null (concatMap (findNonForcePos True) args)
                  then nub (concatMap findForcePos args)
                  else []
    forceFrom i sc = []

    findForcePos (P _ (MN i ff) _)
        | ff == txt "FF" = [i]
    -- Only look under constructors in applications
    findForcePos ap@(App _ f a)
        | (P _ con _, args) <- unApply ap,
          isDConName con ctxt
            = nub $ concatMap findForcePos args
    findForcePos _ = []

    findNonForcePos fok (P _ (MN i ff) _)
        | ff == txt "FF" = if fok then [] else [i]
    -- Look under non-constructors in applications for things which can't
    -- be forced
    findNonForcePos fok ap@(App _ f a)
        | (P _ con _, args) <- unApply ap
            = nub $ concatMap (findNonForcePos (fok && isConName con ctxt)) args
    findNonForcePos _ _ = []

addParamConstraints :: FC -> [Int] -> Type -> [(Name, Type)] -> Idris ()
addParamConstraints fc ps cty cons
   = case getRetTy cty of
          TType cvar -> mapM_ (addConConstraint ps cvar)
                              (map getParamNames cons)
          _ -> return ()
  where
    getParamNames (n, ty) = (ty, getPs ty)

    getPs (Bind n (Pi _ _ _ _) sc)
       = getPs (substV (P Ref n Erased) sc)
    getPs t | (f, args) <- unApply t
       = paramArgs 0 args

    paramArgs i (P _ n _ : args) | i `elem` ps = n : paramArgs (i + 1) args
    paramArgs i (_ : args) = paramArgs (i + 1) args
    paramArgs i [] = []

    addConConstraint ps cvar (ty, pnames) = constraintTy ty
      where
        constraintTy (Bind n (Pi _ _ ty _) sc)
           = case getRetTy ty of
                  TType avar -> do tit <- typeInType
                                   when (not tit) $ do
                                       ctxt <- getContext
                                       let tv = next_tvar ctxt
                                       let con = if n `elem` pnames
                                                    then ULE avar cvar
                                                    else ULT avar cvar
                                       addConstraints fc (tv, [con])
                                       addIBC (IBCConstraint fc con)
                  _ -> return ()
        constraintTy t = return ()

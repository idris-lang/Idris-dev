{-|
Module      : Idris.Elab.Data
Description : Code to elaborate data structures.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Data(elabData) where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.Core.CaseTree
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Coverage
import Idris.DataOpts
import Idris.DeepSeq
import Idris.Delaborate
import Idris.Docstrings
import Idris.DSL
import Idris.Elab.Rewrite
import Idris.Elab.Term
import Idris.Elab.Type
import Idris.Elab.Utils
import Idris.Elab.Value
import Idris.Error
import Idris.Imports
import Idris.Inliner
import Idris.Output (iWarn, iputStrLn, pshow, sendHighlighting)
import Idris.PartialEval
import Idris.Primitives
import Idris.Providers
import IRTS.Lang

import Util.Pretty

import Prelude hiding (id, (.))

import Control.Applicative hiding (Const)
import Control.Category
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict as State
import Data.Char (isLetter, toLower)
import Data.List
import Data.List.Split (splitOn)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Debug.Trace

warnLC :: FC -> Name -> Idris ()
warnLC fc n
   = iWarn fc $ annName n <+> text "has a name which may be implicitly bound."
           <> line <> text "This is likely to lead to problems!"

elabData :: ElabInfo -> SyntaxInfo -> Docstring (Either Err PTerm)-> [(Name, Docstring (Either Err PTerm))] -> FC -> DataOpts -> PData -> Idris ()
elabData info syn doc argDocs fc opts (PLaterdecl n nfc t_in)
    = do let codata = Codata `elem` opts
         logElab 1 (show (fc, doc))
         checkUndefined fc n
         when (implicitable (nsroot n)) $ warnLC fc n
         (cty, _, t, inacc) <- buildType info syn fc [] n t_in

         addIBC (IBCDef n)
         updateContext (addTyDecl n (TCon 0 0) cty) -- temporary, to check cons
         sendHighlighting [(nfc, AnnName n Nothing Nothing Nothing)]

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
         let as = map (const (Left (Msg ""))) (getArgTys cty)

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
         when (any linearArg (map snd cons)) $
            updateContext (setRigCount n Rig1)

         mapM_ totcheck (zip (repeat fc) (map fst cons))
--          mapM_ (checkPositive n) cons

         -- if there's exactly one constructor,
         -- mark both the type and the constructor as detaggable
         case cons of
            [(cn,ct)] -> setDetaggable cn >> setDetaggable n
                >> addIBC (IBCOpt cn) >> addIBC (IBCOpt n)
            _ -> return ()

         -- create an eliminator
         when (DefaultEliminator `elem` opts) $
            evalStateT (elabCaseFun True params n t dcons info) Map.empty
         -- create a case function
         when (DefaultCaseFun `elem` opts) $
            evalStateT (elabCaseFun False params n t dcons info) Map.empty
         -- create a rewriting lemma
         when (n /= sUN "=") $
            elabRewriteLemma info n cty
         -- Emit highlighting info
         sendHighlighting $ [(nfc, AnnName n Nothing Nothing Nothing)] ++
           map (\(_, _, n, nfc, _, _, _) ->
                 (nfc, AnnName n Nothing Nothing Nothing))
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
                newb = addAlist dsParams (inblock info)
                l = liftname info in
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


    getNamePos :: Int -> PTerm -> Name -> Maybe Int
    getNamePos i (PPi _ n _ _ sc) x | n == x = Just i
                                    | otherwise = getNamePos (i + 1) sc x
    getNamePos _ _ _ = Nothing

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

type EliminatorState = StateT (Map.Map String Int) Idris

-- -- Issue #1616 in the issue tracker.
--     https://github.com/idris-lang/Idris-dev/issues/1616
--
-- TODO: Rewrite everything to use idris_implicits instead of manual splitting (or in TT)
-- FIXME: Many things have name starting with elim internally since this was the only purpose in the first edition of the function
-- rename to caseFun to match updated intend
elabCaseFun :: Bool -> [Int] -> Name -> PTerm ->
                  [(Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, FC, PTerm, FC, [Name])] ->
                  ElabInfo -> EliminatorState ()
elabCaseFun ind paramPos n ty cons info = do
  elimLog "Elaborating case function"
  put (Map.fromList $ zip (concatMap (\(_, p, _, _, ty, _, _) -> (map show $ boundNamesIn ty) ++ map (show . fst) p) cons ++ (map show $ boundNamesIn ty)) (repeat 0))
  let (cnstrs, _) = splitPi ty
  let (splittedTy@(pms, idxs)) = splitPms cnstrs
  generalParams <- namePis False pms
  motiveIdxs    <- namePis False idxs
  let motive = mkMotive n paramPos generalParams motiveIdxs
  consTerms <- mapM (\(c@(_, _, cnm, _, _, _, _)) -> do
                               let casefunt = if ind then "elim_" else "case_"
                               name <- freshName $ casefunt ++ simpleName cnm
                               consTerm <- extractConsTerm c generalParams
                               return (name, expl, consTerm)) cons
  scrutineeIdxs <- namePis False idxs
  let motiveConstr = [(motiveName, expl, motive)]
  let scrutinee = (scrutineeName, expl, applyCons n (interlievePos paramPos generalParams scrutineeIdxs 0))
  let eliminatorTy = piConstr (generalParams ++ motiveConstr ++ consTerms ++ scrutineeIdxs ++ [scrutinee]) (applyMotive (map (\(n,_,_) -> PRef elimFC [] n) scrutineeIdxs) (PRef elimFC [] scrutineeName))
  let eliminatorTyDecl = PTy (fmap (const (Left $ Msg "")) . parseDocstring . T.pack $ show n) [] defaultSyntax elimFC [TotalFn] elimDeclName elimFC eliminatorTy
  let clauseConsElimArgs = map getPiName consTerms
  let clauseGeneralArgs' = map getPiName generalParams ++ [motiveName] ++ clauseConsElimArgs
  let clauseGeneralArgs  = map (\arg -> pexp (PRef elimFC [] arg)) clauseGeneralArgs'
  let elimSig = "-- case function signature: " ++ showTmImpls eliminatorTy
  elimLog elimSig
  eliminatorClauses <- mapM (\(cns, cnsElim) -> generateEliminatorClauses cns cnsElim clauseGeneralArgs generalParams) (zip cons clauseConsElimArgs)
  let eliminatorDef = PClauses elimFC [TotalFn] elimDeclName eliminatorClauses
  elimLog $ "-- case function definition: " ++ (show . showDeclImp verbosePPOption) eliminatorDef
  State.lift $ idrisCatch (rec_elabDecl info EAll info eliminatorTyDecl)
                    (ierror . Elaborating "type declaration of " elimDeclName Nothing)
  -- Do not elaborate clauses if there aren't any
  case eliminatorClauses of
    [] -> State.lift $ solveDeferred elimFC elimDeclName -- Remove meta-variable for type
    _  -> State.lift $ idrisCatch (rec_elabDecl info EAll info eliminatorDef)
                    (ierror . Elaborating "clauses of " elimDeclName Nothing)
  where elimLog :: String -> EliminatorState ()
        elimLog s = State.lift (logElab 2 s)

        elimFC :: FC
        elimFC = fileFC $ "(casefun " ++ show n ++ ")"

        elimDeclName :: Name
        elimDeclName = if ind then SN . ElimN $ n else SN . CaseN (FC' elimFC) $ n

        applyNS :: Name -> [String] -> Name
        applyNS n []  = n
        applyNS n ns  = sNS n ns

        splitPi :: PTerm -> ([(Name, Plicity, PTerm)], PTerm)
        splitPi = splitPi' []
          where splitPi' :: [(Name, Plicity, PTerm)] -> PTerm -> ([(Name, Plicity, PTerm)], PTerm)
                splitPi' acc (PPi pl n _ tyl tyr) = splitPi' ((n, pl, tyl):acc) tyr
                splitPi' acc t                    = (reverse acc, t)

        splitPms :: [(Name, Plicity, PTerm)] -> ([(Name, Plicity, PTerm)], [(Name, Plicity, PTerm)])
        splitPms cnstrs = (map fst pms, map fst idxs)
           where (pms, idxs) = partition (\c -> snd c `elem` paramPos) (zip cnstrs [0..])

        isMachineGenerated :: Name -> Bool
        isMachineGenerated (MN _ _) = True
        isMachineGenerated _        = False

        namePis :: Bool -> [(Name, Plicity, PTerm)] -> EliminatorState [(Name, Plicity, PTerm)]
        namePis keepOld pms = do names <- mapM (mkPiName keepOld) pms
                                 let oldNames = map fst names
                                 let params   = map snd names
                                 return $ map (\(n, pl, ty) -> (n, pl, removeParamPis oldNames params ty)) params

        mkPiName :: Bool -> (Name, Plicity, PTerm) -> EliminatorState (Name, (Name, Plicity, PTerm))
        mkPiName keepOld (n, pl, piarg) | not (isMachineGenerated n) && keepOld = do return (n, (n, pl, piarg))
        mkPiName _ (oldName, pl, piarg) =  do name <- freshName $ keyOf piarg
                                              return (oldName, (name, pl, piarg))
          where keyOf :: PTerm -> String
                keyOf (PRef _ _ name) | isLetter (nameStart name) = (toLower $ nameStart name):"__"
                keyOf (PApp _ tyf _) = keyOf tyf
                keyOf (PType _) = "ty__"
                keyOf _     = "carg__"
                nameStart :: Name -> Char
                nameStart n = nameStart' (simpleName n)
                  where nameStart' :: String -> Char
                        nameStart' "" = ' '
                        nameStart' ns = head ns

        simpleName :: Name -> String
        simpleName (NS n _) = simpleName n
        simpleName (MN i n) = str n ++ show i
        simpleName n        = show n

        nameSpaces :: Name -> [String]
        nameSpaces (NS _ ns) = map str ns
        nameSpaces _         = []

        freshName :: String -> EliminatorState Name
        freshName key = do
          nameMap <- get
          let i = fromMaybe 0 (Map.lookup key nameMap)
          let name = uniqueName (sUN (key ++ show i)) (map (\(nm, nb) -> sUN (nm ++ show nb)) $ Map.toList nameMap)
          put $ Map.insert key (i+1) nameMap
          return name

        scrutineeName :: Name
        scrutineeName = sUN "scrutinee"

        scrutineeArgName :: Name
        scrutineeArgName = sUN "scrutineeArg"

        motiveName :: Name
        motiveName = sUN "prop"

        mkMotive :: Name -> [Int] -> [(Name, Plicity, PTerm)] -> [(Name, Plicity, PTerm)] -> PTerm
        mkMotive n paramPos params indicies =
          let scrutineeTy = (scrutineeArgName, expl, applyCons n (interlievePos paramPos params indicies 0))
          in piConstr (indicies ++ [scrutineeTy]) (PType elimFC)

        piConstr :: [(Name, Plicity, PTerm)] -> PTerm -> PTerm
        piConstr [] ty = ty
        piConstr ((n, pl, tyb):tyr) ty = PPi pl n elimFC tyb (piConstr tyr ty)

        interlievePos :: [Int] -> [a] -> [a] -> Int -> [a]
        interlievePos idxs []     l2     i = l2
        interlievePos idxs l1     []     i = l1
        interlievePos idxs (x:xs) l2     i | i `elem` idxs = x:(interlievePos idxs xs l2 (i+1))
        interlievePos idxs l1     (y:ys) i = y:(interlievePos idxs l1 ys (i+1))

        replaceParams :: [Int] -> [(Name, Plicity, PTerm)] -> PTerm -> PTerm
        replaceParams paramPos params cns =
          let (_, cnsResTy) = splitPi cns
          in case cnsResTy of
               PApp _ _ args ->
                let oldParams = paramNamesOf 0 paramPos args
                in removeParamPis oldParams params cns
               _ -> cns

        removeParamPis :: [Name] -> [(Name, Plicity, PTerm)] -> PTerm -> PTerm
        removeParamPis oldParams params (PPi pl n fc tyb tyr) =
          case findIndex (== n) oldParams of
            Nothing -> (PPi pl n fc (removeParamPis oldParams params tyb) (removeParamPis oldParams params tyr))
            Just i  -> (removeParamPis oldParams params tyr)
        removeParamPis oldParams params (PRef _ _ n) =
          case findIndex (== n) oldParams of
               Nothing -> (PRef elimFC [] n)
               Just i  -> let (newname,_,_) = params !! i in (PRef elimFC [] (newname))
        removeParamPis oldParams params (PApp _ cns args) =
          PApp elimFC (removeParamPis oldParams params cns) $ replaceParamArgs args
            where replaceParamArgs :: [PArg] -> [PArg]
                  replaceParamArgs []          = []
                  replaceParamArgs (arg:args)  =
                    case extractName (getTm arg) of
                      []   -> arg:replaceParamArgs args
                      [n]  ->
                        case findIndex (== n) oldParams of
                          Nothing -> arg:replaceParamArgs args
                          Just i  -> let (newname,_,_) = params !! i in arg {getTm = PRef elimFC [] newname}:replaceParamArgs args
        removeParamPis oldParams params t = t

        paramNamesOf :: Int -> [Int] -> [PArg] -> [Name]
        paramNamesOf i paramPos []          = []
        paramNamesOf i paramPos (arg:args)  = (if i `elem` paramPos then extractName (getTm arg) else []) ++ paramNamesOf (i+1) paramPos args

        extractName :: PTerm -> [Name]
        extractName (PRef _ _ n) = [n]
        extractName _            = []

        splitArgPms :: PTerm -> ([PTerm], [PTerm])
        splitArgPms (PApp _ f args) = splitArgPms' args
          where splitArgPms' :: [PArg] -> ([PTerm], [PTerm])
                splitArgPms' cnstrs = (map (getTm . fst) pms, map (getTm . fst) idxs)
                    where (pms, idxs) = partition (\c -> snd c `elem` paramPos) (zip cnstrs [0..])
        splitArgPms _                 = ([],[])


        implicitIndexes :: (Docstring (Either Err PTerm), Name, PTerm, FC, [Name]) -> EliminatorState [(Name, Plicity, PTerm)]
        implicitIndexes (cns@(doc, cnm, ty, fc, fs)) = do
          i <-  State.lift getIState
          implargs' <- case lookupCtxt cnm (idris_implicits i) of
            [] -> do fail $ "Error while showing implicits for " ++ show cnm
            [args] -> do return args
            _ -> do fail $ "Ambigous name for " ++ show cnm
          let implargs = mapMaybe convertImplPi implargs'
          let (_, cnsResTy) = splitPi ty
          case cnsResTy of
             PApp _ _ args ->
              let oldParams = paramNamesOf 0 paramPos args
              in return $ filter (\(n,_,_) -> not (n `elem` oldParams))implargs
             _ -> return implargs

        extractConsTerm :: (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, FC, PTerm, FC, [Name]) -> [(Name, Plicity, PTerm)] -> EliminatorState PTerm
        extractConsTerm (doc, argDocs, cnm, _, ty, fc, fs) generalParameters = do
          let cons' = replaceParams paramPos generalParameters ty
          let (args, resTy) = splitPi cons'
          implidxs <- implicitIndexes (doc, cnm, ty, fc, fs)
          consArgs <- namePis False args
          let recArgs = findRecArgs consArgs
          let recMotives = if ind then map applyRecMotive recArgs else []
          let (_, consIdxs) = splitArgPms resTy
          return $ piConstr (implidxs ++ consArgs ++ recMotives) (applyMotive consIdxs (applyCons cnm consArgs))
            where applyRecMotive :: (Name, Plicity, PTerm) -> (Name, Plicity, PTerm)
                  applyRecMotive (n,_,ty)  = (sUN $ "ih" ++ simpleName n, expl, applyMotive idxs (PRef elimFC [] n))
                      where (_, idxs) = splitArgPms ty

        findRecArgs :: [(Name, Plicity, PTerm)] -> [(Name, Plicity, PTerm)]
        findRecArgs []                            = []
        findRecArgs (ty@(_,_,PRef _ _ tn):rs)            | simpleName tn == simpleName n = ty:findRecArgs rs
        findRecArgs (ty@(_,_,PApp _ (PRef _ _ tn) _):rs) | simpleName tn == simpleName n = ty:findRecArgs rs
        findRecArgs (ty:rs)                                                              = findRecArgs rs

        applyCons :: Name -> [(Name, Plicity, PTerm)] -> PTerm
        applyCons tn targs = PApp elimFC (PRef elimFC [] tn) (map convertArg targs)

        convertArg :: (Name, Plicity, PTerm) -> PArg
        convertArg (n, _, _)      = pexp (PRef elimFC [] n)

        applyMotive :: [PTerm] -> PTerm -> PTerm
        applyMotive idxs t = PApp elimFC (PRef elimFC [] motiveName) (map pexp idxs ++ [pexp t])

        getPiName :: (Name, Plicity, PTerm) -> Name
        getPiName (name,_,_) = name

        convertImplPi :: PArg -> Maybe (Name, Plicity, PTerm)
        convertImplPi (PImp {getTm = t, pname = n}) = Just (n, expl, t)
        convertImplPi _                             = Nothing

        generateEliminatorClauses :: (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, FC, PTerm, FC, [Name]) -> Name -> [PArg] -> [(Name, Plicity, PTerm)] -> EliminatorState PClause
        generateEliminatorClauses (doc, _, cnm, _, ty, fc, fs) cnsElim generalArgs generalParameters = do
          let cons' = replaceParams paramPos generalParameters ty
          let (args, resTy) = splitPi cons'
          i <- State.lift getIState
          implidxs <- implicitIndexes (doc, cnm, ty, fc, fs)
          let (_, generalIdxs') = splitArgPms resTy
          let generalIdxs = map pexp generalIdxs'
          consArgs <- namePis False args
          let lhsPattern = PApp elimFC (PRef elimFC [] elimDeclName) (generalArgs ++ generalIdxs ++ [pexp $ applyCons cnm consArgs])
          let recArgs = findRecArgs consArgs
          let recElims = if ind then map applyRecElim recArgs else []
          let rhsExpr    = PApp elimFC (PRef elimFC [] cnsElim) (map convertArg implidxs ++ map convertArg consArgs ++ recElims)
          return $ PClause elimFC elimDeclName lhsPattern [] rhsExpr []
            where applyRecElim :: (Name, Plicity, PTerm) -> PArg
                  applyRecElim (constr@(recCnm,_,recTy)) = pexp $ PApp elimFC (PRef elimFC [] elimDeclName) (generalArgs ++ map pexp idxs ++ [pexp $ PRef elimFC [] recCnm])
                    where (_, idxs) = splitArgPms recTy

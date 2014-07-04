{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards #-}

module Idris.ElabDecls where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.DSL
import Idris.Error
import Idris.Delaborate
import Idris.Imports
import Idris.ElabTerm
import Idris.Coverage
import Idris.DataOpts
import Idris.Providers
import Idris.Primitives
import Idris.Inliner
import Idris.PartialEval
import Idris.DeepSeq
import Idris.Output (iputStrLn, pshow, iWarn)
import IRTS.Lang

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.Typecheck
import Idris.Core.CaseTree

import Idris.Docstrings

import Prelude hiding (id, (.))
import Control.Category

import Control.Applicative hiding (Const)
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict as State
import Data.List
import Data.Maybe
import Debug.Trace

import qualified Data.Map as Map
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Char(isLetter, toLower)
import Data.List.Split (splitOn)

import Util.Pretty(pretty, text)

recheckC fc env t
    = do -- t' <- applyOpts (forget t) (doesn't work, or speed things up...)
         ctxt <- getContext
         (tm, ty, cs) <- tclift $ case recheck ctxt env (forget t) t of
                                   Error e -> tfail (At fc e)
                                   OK x -> return x
         addConstraints fc cs
         return (tm, ty)


checkDef fc ns = checkAddDef False True fc ns

checkAddDef add toplvl fc [] = return []
checkAddDef add toplvl fc ((n, (i, top, t)) : ns) 
               = do ctxt <- getContext
                    (t', _) <- recheckC fc [] t
                    when add $ do addDeferred [(n, (i, top, t, toplvl))]
                                  addIBC (IBCDef n)
                    ns' <- checkAddDef add toplvl fc ns
                    return ((n, (i, top, t')) : ns')
--                     mapM (\(n, (i, top, t)) -> do (t', _) <- recheckC fc [] t
--                                                   return (n, (i, top, t'))) ns

-- | Elaborate a top-level type declaration - for example, "foo : Int -> Int".
elabType :: ElabInfo -> SyntaxInfo -> Docstring -> [(Name, Docstring)] ->
            FC -> FnOpts -> Name -> PTerm -> Idris Type
elabType = elabType' False

elabType' :: Bool -> -- normalise it
             ElabInfo -> SyntaxInfo -> Docstring -> [(Name, Docstring)] ->
             FC -> FnOpts -> Name -> PTerm -> Idris Type
elabType' norm info syn doc argDocs fc opts n ty' = {- let ty' = piBind (params info) ty_in
                                                       n  = liftname info n_in in    -}
      do checkUndefined fc n
         ctxt <- getContext
         i <- getIState

         logLvl 5 $ show n ++ " pre-type " ++ showTmImpls ty'
         ty' <- addUsingConstraints syn fc ty'
         ty' <- implicit info syn n ty'

         let ty    = addImpl i ty'
             inacc = inaccessibleArgs 0 ty
         logLvl 5 $ show n ++ " type pre-addimpl " ++ showTmImpls ty'
         logLvl 5 $ show n ++ " type " ++ showTmImpls ty
         logLvl 3 $ show n ++ ": inaccessible arguments: " ++ show inacc

         ((tyT, defer, is), log) <-
               tclift $ elaborate ctxt n (TType (UVal 0)) []
                        (errAt "type of " n (erun fc (build i info False [] n ty)))
         ds <- checkAddDef True False fc defer
         -- if the type is not complete, note that we'll need to infer
         -- things later (for solving metavariables)
         when (not (null ds)) $ addTyInferred n

         mapM_ (elabCaseBlock info opts) is
         ctxt <- getContext
         logLvl 5 $ "Rechecking"
         logLvl 6 $ show tyT
         (cty, _)   <- recheckC fc [] tyT
         addStatics n cty ty'
         logLvl 6 $ "Elaborated to " ++ showEnvDbg [] tyT
         logLvl 2 $ "Rechecked to " ++ show cty
         let nty = cty -- normalise ctxt [] cty
         -- if the return type is something coinductive, freeze the definition
         let nty' = normalise ctxt [] nty

         -- Add normalised type to internals
         rep <- useREPL
         when rep $ do
           addInternalApp (fc_fname fc) (fst . fc_start $ fc) (mergeTy ty' (delab i nty')) -- TODO: Should use span instead of line and filename?
           addIBC (IBCLineApp (fc_fname fc) (fst . fc_start $ fc) (mergeTy ty' (delab i nty')))

         let (t, _) = unApply (getRetTy nty')
         let corec = case t of
                        P _ rcty _ -> case lookupCtxt rcty (idris_datatypes i) of
                                        [TI _ True _ _ _] -> True
                                        _ -> False
                        _ -> False
         -- Productivity checking now via checking for guarded 'Delay' 
         let opts' = opts -- if corec then (Coinductive : opts) else opts
         let usety = if norm then nty' else nty
         ds <- checkDef fc [(n, (-1, Nothing, usety))]
         addIBC (IBCDef n)
         let ds' = map (\(n, (i, top, t)) -> (n, (i, top, t, True))) ds
         addDeferred ds'
         setFlags n opts'
         checkDocs fc argDocs ty
         addDocStr n doc argDocs
         addIBC (IBCDoc n)
         addIBC (IBCFlags n opts')
         fputState (opt_inaccessible . ist_optimisation n) inacc
         addIBC (IBCOpt n)
         when (Implicit `elem` opts') $ do addCoercion n
                                           addIBC (IBCCoercion n)

         -- If the function is declared as an error handler and the language
         -- extension is enabled, then add it to the list of error handlers.
         errorReflection <- fmap (elem ErrorReflection . idris_language_extensions) getIState
         when (ErrorHandler `elem` opts) $ do
           if errorReflection
             then
               -- TODO: Check that the declared type is the correct type for an error handler:
               -- handler : List (TTName, TT) -> Err -> ErrorReport - for now no ctxt
               if tyIsHandler nty'
                 then do i <- getIState
                         putIState $ i { idris_errorhandlers = idris_errorhandlers i ++ [n] }
                         addIBC (IBCErrorHandler n)
                 else ifail $ "The type " ++ show nty' ++ " is invalid for an error handler"
             else ifail "Error handlers can only be defined when the ErrorReflection language extension is enabled."
         return usety
  where
    -- for making an internalapp, we only want the explicit ones, and don't
    -- want the parameters, so just take the arguments which correspond to the
    -- user declared explicit ones
    mergeTy (PPi e n ty sc) (PPi e' _ _ sc')
         | e == e' = PPi e n ty (mergeTy sc sc')
         | otherwise = mergeTy sc sc'
    mergeTy _ sc = sc

    err = txt "Err"
    maybe = txt "Maybe"
    lst = txt "List"
    errrep = txt "ErrorReportPart"

    tyIsHandler (Bind _ (Pi (P _ (NS (UN e) ns1) _))
                        (App (P _ (NS (UN m) ns2) _)
                             (App (P _ (NS (UN l) ns3) _)
                                  (P _ (NS (UN r) ns4) _))))
        | e == err && m == maybe && l == lst && r == errrep
        , ns1 == map txt ["Errors","Reflection","Language"]
        , ns2 == map txt ["Maybe", "Prelude"]
        , ns3 == map txt ["List", "Prelude"]
        , ns4 == map txt ["Errors","Reflection","Language"] = True
    tyIsHandler _                                           = False

-- Get the list of (index, name) of inaccessible arguments from the type.
inaccessibleArgs :: Int -> PTerm -> [(Int, Name)]
inaccessibleArgs i (PPi (Imp _ _ _) n Placeholder t)
        = (i,n) : inaccessibleArgs (i+1) t  -- unbound implicit
inaccessibleArgs i (PPi plicity n ty t)
    | InaccessibleArg `elem` pargopts plicity
        = (i,n) : inaccessibleArgs (i+1) t  -- an .{erased : Implicit}
    | otherwise
        = inaccessibleArgs (i+1) t      -- a {regular : Implicit}
inaccessibleArgs _ _ = []

elabPostulate :: ElabInfo -> SyntaxInfo -> Docstring ->
                 FC -> FnOpts -> Name -> PTerm -> Idris ()
elabPostulate info syn doc fc opts n ty = do
    elabType info syn doc [] fc opts n ty
    putIState . (\ist -> ist{ idris_postulates = S.insert n (idris_postulates ist) }) =<< getIState
    addIBC (IBCPostulate n)

    -- remove it from the deferred definitions list
    solveDeferred n

elabData :: ElabInfo -> SyntaxInfo -> Docstring -> [(Name, Docstring)] -> FC -> DataOpts -> PData -> Idris ()
elabData info syn doc argDocs fc opts (PLaterdecl n t_in)
    = do let codata = Codata `elem` opts
         iLOG (show (fc, doc))
         checkUndefined fc n
         ctxt <- getContext
         i <- getIState
         -- TODO think: something more in info?
         t_in <- implicit info syn n t_in
         let t = addImpl i t_in
         ((t', defer, is), log) <- tclift $ elaborate ctxt n (TType (UVal 0)) []
                                            (erun fc (build i info False [] n t))
         def' <- checkDef fc defer
         let def'' = map (\(n, (i, top, t)) -> (n, (i, top, t, True))) def'
         addDeferredTyCon def''
         addIBC (IBCDef n)
         mapM_ (elabCaseBlock info []) is
         (cty, _)  <- recheckC fc [] t'
         logLvl 2 $ "---> " ++ show cty
         updateContext (addTyDecl n (TCon 0 0) cty) -- temporary, to check cons

elabData info syn doc argDocs fc opts (PDatadecl n t_in dcons)
    = do let codata = Codata `elem` opts
         iLOG (show fc)
         undef <- isUndefined fc n
         ctxt <- getContext
         i <- getIState
         t_in <- implicit info syn n t_in
         let t = addImpl i t_in
         ((t', defer, is), log) <-
             tclift $ elaborate ctxt n (TType (UVal 0)) []
                  (errAt "data declaration " n (erun fc (build i info False [] n t)))
         def' <- checkDef fc defer
         let def'' = map (\(n, (i, top, t)) -> (n, (i, top, t, True))) def'
         -- if n is defined already, make sure it is just a type declaration
         -- with the same type we've just elaborated
         checkDefinedAs fc n t' (tt_ctxt i)
         addDeferredTyCon def''
         mapM_ (elabCaseBlock info []) is
         (cty, _)  <- recheckC fc [] t'
         logLvl 2 $ "---> " ++ show cty
         -- temporary, to check cons
         when undef $ updateContext (addTyDecl n (TCon 0 0) cty)
         let cnameinfo = cinfo info (map cname dcons)
         cons <- mapM (elabCon cnameinfo syn n codata) dcons
         ttag <- getName
         i <- getIState
         let as = map (const Nothing) (getArgTys cty)
         let params = findParams  (map snd cons)
         logLvl 2 $ "Parameters : " ++ show params
         -- TI contains information about mutually declared types - this will
         -- be updated when the mutual block is complete
         putIState (i { idris_datatypes =
                          addDef n (TI (map fst cons) codata opts params [n])
                                             (idris_datatypes i) })
         addIBC (IBCDef n)
         addIBC (IBCData n)
         checkDocs fc argDocs t_in
         addDocStr n doc argDocs
         addIBC (IBCDoc n)
         let metainf = DataMI params
         addIBC (IBCMetaInformation n metainf)
         -- TMP HACK! Make this a data option
         updateContext (addDatatype (Data n ttag cty cons))
         updateContext (setMetaInformation n metainf)
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
  where
        setDetaggable :: Name -> Idris ()
        setDetaggable n = do
            ist <- getIState
            let opt = idris_optimisation ist
            case lookupCtxt n opt of
                [oi] -> putIState ist{ idris_optimisation = addDef n oi{ detaggable = True } opt }
                _    -> putIState ist{ idris_optimisation = addDef n (Optimise [] True) opt }

        checkDefinedAs fc n t ctxt 
            = case lookupDef n ctxt of
                   [] -> return ()
                   [TyDecl _ ty] ->
                      case converts ctxt [] t ty of
                           OK () -> return ()
                           _ -> tclift $ tfail (At fc (AlreadyDefined n))
                   _ -> tclift $ tfail (At fc (AlreadyDefined n))
        -- parameters are names which are unchanged across the structure,
        -- which appear exactly once in the return type of a constructor

        -- First, find all applications of the constructor, then check over
        -- them for repeated arguments

        findParams :: [Type] -> [Int]
        findParams ts = let allapps = concatMap getDataApp ts in
                            paramPos allapps

        paramPos [] = []
        paramPos (args : rest)
              = dropNothing $ keepSame (zip [0..] args) rest

        dropNothing [] = []
        dropNothing ((x, Nothing) : ts) = dropNothing ts
        dropNothing ((x, _) : ts) = x : dropNothing ts

        keepSame :: [(Int, Maybe Name)] -> [[Maybe Name]] ->
                    [(Int, Maybe Name)]
        keepSame as [] = as
        keepSame as (args : rest) = keepSame (update as args) rest
          where
            update [] _ = []
            update _ [] = []
            update ((n, Just x) : as) (Just x' : args)
                | x == x' = (n, Just x) : update as args
            update ((n, _) : as) (_ : args) = (n, Nothing) : update as args

        getDataApp :: Type -> [[Maybe Name]]
        getDataApp f@(App _ _)
            | (P _ d _, args) <- unApply f
                   = if (d == n) then [mParam args args] else []
        getDataApp (Bind n (Pi t) sc)
            = getDataApp t ++ getDataApp (instantiate (P Bound n t) sc)
        getDataApp _ = []

        -- keep the arguments which are single names, which don't appear
        -- elsewhere

        mParam args [] = []
        mParam args (P Bound n _ : rest)
               | count n args == 1
                  = Just n : mParam args rest
            where count n [] = 0
                  count n (t : ts)
                       | n `elem` freeNames t = 1 + count n ts
                       | otherwise = count n ts
        mParam args (_ : rest) = Nothing : mParam args rest

        cname (_, _, n, _, _, _) = n

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

type EliminatorState = StateT (Map.Map String Int) Idris

-- TODO: Rewrite everything to use idris_implicits instead of manual splitting (or in TT)
-- FIXME: Many things have name starting with elim internally since this was the only purpose in the first edition of the function
-- rename to caseFun to match updated intend
elabCaseFun :: Bool -> [Int] -> Name -> PTerm ->
                  [(Docstring, [(Name, Docstring)], Name, PTerm, FC, [Name])] ->
                  ElabInfo -> EliminatorState ()
elabCaseFun ind paramPos n ty cons info = do
  elimLog $ "Elaborating case function"
  put (Map.fromList $ zip (concatMap (\(_, p, _, ty, _, _) -> (map show $ boundNamesIn ty) ++ map (show . fst) p) cons ++ (map show $ boundNamesIn ty)) (repeat 0))
  let (cnstrs, _) = splitPi ty
  let (splittedTy@(pms, idxs)) = splitPms cnstrs
  generalParams <- namePis False pms
  motiveIdxs    <- namePis False idxs
  let motive = mkMotive n paramPos generalParams motiveIdxs
  consTerms <- mapM (\(c@(_, _, cnm, _, _, _)) -> do
                               let casefunt = if ind then "elim_" else "case_"
                               name <- freshName $ casefunt ++ simpleName cnm
                               consTerm <- extractConsTerm c generalParams
                               return (name, expl, consTerm)) cons
  scrutineeIdxs <- namePis False idxs
  let motiveConstr = [(motiveName, expl, motive)]
  let scrutinee = (scrutineeName, expl, applyCons n (interlievePos paramPos generalParams scrutineeIdxs 0))
  let eliminatorTy = piConstr (generalParams ++ motiveConstr ++ consTerms ++ scrutineeIdxs ++ [scrutinee]) (applyMotive (map (\(n,_,_) -> PRef elimFC n) scrutineeIdxs) (PRef elimFC scrutineeName))
  let eliminatorTyDecl = PTy (parseDocstring . T.pack $ show n) [] defaultSyntax elimFC [TotalFn] elimDeclName eliminatorTy
  let clauseConsElimArgs = map getPiName consTerms
  let clauseGeneralArgs' = map getPiName generalParams ++ [motiveName] ++ clauseConsElimArgs
  let clauseGeneralArgs  = map (\arg -> pexp (PRef elimFC arg)) clauseGeneralArgs'
  let elimSig = "-- case function signature: " ++ showTmImpls eliminatorTy
  elimLog elimSig
  eliminatorClauses <- mapM (\(cns, cnsElim) -> generateEliminatorClauses cns cnsElim clauseGeneralArgs generalParams) (zip cons clauseConsElimArgs)
  let eliminatorDef = PClauses emptyFC [TotalFn] elimDeclName eliminatorClauses
  elimLog $ "-- case function definition: " ++ (show . showDeclImp verbosePPOption) eliminatorDef
  State.lift $ idrisCatch (elabDecl EAll info eliminatorTyDecl) (\err -> return ())
  -- Do not elaborate clauses if there aren't any
  case eliminatorClauses of
    [] -> State.lift $ solveDeferred elimDeclName -- Remove meta-variable for type
    _  -> State.lift $ idrisCatch (elabDecl EAll info eliminatorDef) (\err -> return ())
  where elimLog :: String -> EliminatorState ()
        elimLog s = State.lift (logLvl 2 s)

        elimFC :: FC
        elimFC = fileFC "(casefun)"

        elimDeclName :: Name
        elimDeclName = if ind then SN . ElimN $ n else SN . CaseN $ n

        applyNS :: Name -> [String] -> Name
        applyNS n []  = n
        applyNS n ns  = sNS n ns

        splitPi :: PTerm -> ([(Name, Plicity, PTerm)], PTerm)
        splitPi = splitPi' []
          where splitPi' :: [(Name, Plicity, PTerm)] -> PTerm -> ([(Name, Plicity, PTerm)], PTerm)
                splitPi' acc (PPi pl n tyl tyr) = splitPi' ((n, pl, tyl):acc) tyr
                splitPi' acc t                  = (reverse acc, t)

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
                keyOf (PRef _ name) | isLetter (nameStart name) = (toLower $ nameStart name):"__"
                keyOf (PApp _ tyf _) = keyOf tyf
                keyOf PType = "ty__"
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
          in piConstr (indicies ++ [scrutineeTy]) PType

        piConstr :: [(Name, Plicity, PTerm)] -> PTerm -> PTerm
        piConstr [] ty = ty
        piConstr ((n, pl, tyb):tyr) ty = PPi pl n tyb (piConstr tyr ty)

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
        removeParamPis oldParams params (PPi pl n tyb tyr) =
          case findIndex (== n) oldParams of
            Nothing -> (PPi pl n (removeParamPis oldParams params tyb) (removeParamPis oldParams params tyr))
            Just i  -> (removeParamPis oldParams params tyr)
        removeParamPis oldParams params (PRef _ n) = 
          case findIndex (== n) oldParams of
               Nothing -> (PRef elimFC n)
               Just i  -> let (newname,_,_) = params !! i in (PRef elimFC (newname))
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
                          Just i  -> let (newname,_,_) = params !! i in arg {getTm = PRef elimFC newname}:replaceParamArgs args
        removeParamPis oldParams params t = t

        paramNamesOf :: Int -> [Int] -> [PArg] -> [Name]
        paramNamesOf i paramPos []          = []
        paramNamesOf i paramPos (arg:args)  = (if i `elem` paramPos then extractName (getTm arg) else []) ++ paramNamesOf (i+1) paramPos args

        extractName :: PTerm -> [Name]
        extractName (PRef _ n) = [n]
        extractName _          = []

        splitArgPms :: PTerm -> ([PTerm], [PTerm])
        splitArgPms (PApp _ f args) = splitArgPms' args
          where splitArgPms' :: [PArg] -> ([PTerm], [PTerm])
                splitArgPms' cnstrs = (map (getTm . fst) pms, map (getTm . fst) idxs)
                    where (pms, idxs) = partition (\c -> snd c `elem` paramPos) (zip cnstrs [0..])
        splitArgPms _                 = ([],[])


        implicitIndexes :: (Docstring, Name, PTerm, FC, [Name]) -> EliminatorState [(Name, Plicity, PTerm)]
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

        extractConsTerm :: (Docstring, [(Name, Docstring)], Name, PTerm, FC, [Name]) -> [(Name, Plicity, PTerm)] -> EliminatorState PTerm
        extractConsTerm (doc, argDocs, cnm, ty, fc, fs) generalParameters = do
          let cons' = replaceParams paramPos generalParameters ty
          let (args, resTy) = splitPi cons'
          implidxs <- implicitIndexes (doc, cnm, ty, fc, fs)
          consArgs <- namePis False args
          let recArgs = findRecArgs consArgs
          let recMotives = if ind then map applyRecMotive recArgs else []
          let (_, consIdxs) = splitArgPms resTy
          return $ piConstr (implidxs ++ consArgs ++ recMotives) (applyMotive consIdxs (applyCons cnm consArgs))
            where applyRecMotive :: (Name, Plicity, PTerm) -> (Name, Plicity, PTerm)
                  applyRecMotive (n,_,ty)  = (sUN $ "ih" ++ simpleName n, expl, applyMotive idxs (PRef elimFC n))
                      where (_, idxs) = splitArgPms ty

        findRecArgs :: [(Name, Plicity, PTerm)] -> [(Name, Plicity, PTerm)]
        findRecArgs []                            = []
        findRecArgs (ty@(_,_,PRef _ tn):rs)            | simpleName tn == simpleName n = ty:findRecArgs rs
        findRecArgs (ty@(_,_,PApp _ (PRef _ tn) _):rs) | simpleName tn == simpleName n = ty:findRecArgs rs
        findRecArgs (ty:rs)                                                            = findRecArgs rs

        applyCons :: Name -> [(Name, Plicity, PTerm)] -> PTerm
        applyCons tn targs = PApp elimFC (PRef elimFC tn) (map convertArg targs)

        convertArg :: (Name, Plicity, PTerm) -> PArg
        convertArg (n, _, _)      = pexp (PRef elimFC n)

        applyMotive :: [PTerm] -> PTerm -> PTerm
        applyMotive idxs t = PApp elimFC (PRef elimFC motiveName) (map pexp idxs ++ [pexp t])

        getPiName :: (Name, Plicity, PTerm) -> Name
        getPiName (name,_,_) = name

        convertImplPi :: PArg -> Maybe (Name, Plicity, PTerm)
        convertImplPi (PImp {getTm = t, pname = n}) = Just (n, expl, t)
        convertImplPi _                             = Nothing

        generateEliminatorClauses :: (Docstring, [(Name, Docstring)], Name, PTerm, FC, [Name]) -> Name -> [PArg] -> [(Name, Plicity, PTerm)] -> EliminatorState PClause
        generateEliminatorClauses (doc, _, cnm, ty, fc, fs) cnsElim generalArgs generalParameters = do
          let cons' = replaceParams paramPos generalParameters ty
          let (args, resTy) = splitPi cons'
          i <- State.lift getIState
          implidxs <- implicitIndexes (doc, cnm, ty, fc, fs)
          let (_, generalIdxs') = splitArgPms resTy
          let generalIdxs = map pexp generalIdxs'
          consArgs <- namePis False args
          let lhsPattern = PApp elimFC (PRef elimFC elimDeclName) (generalArgs ++ generalIdxs ++ [pexp $ applyCons cnm consArgs])
          let recArgs = findRecArgs consArgs
          let recElims = if ind then map applyRecElim recArgs else []
          let rhsExpr    = PApp elimFC (PRef elimFC cnsElim) (map convertArg implidxs ++ map convertArg consArgs ++ recElims)
          return $ PClause elimFC elimDeclName lhsPattern [] rhsExpr []
            where applyRecElim :: (Name, Plicity, PTerm) -> PArg
                  applyRecElim (constr@(recCnm,_,recTy)) = pexp $ PApp elimFC (PRef elimFC elimDeclName) (generalArgs ++ map pexp idxs ++ [pexp $ PRef elimFC recCnm])
                    where (_, idxs) = splitArgPms recTy

-- | Elaborate primitives

elabPrims :: Idris ()
elabPrims = do mapM_ (elabDecl EAll toplevel)
                     (map (\(opt, decl, docs, argdocs) -> PData docs argdocs defaultSyntax (fileFC "builtin") opt decl)
                        (zip4
                         [inferOpts, unitOpts, falseOpts, pairOpts, eqOpts]
                         [inferDecl, unitDecl, falseDecl, pairDecl, eqDecl]
                         [emptyDocstring, unitDoc, falseDoc, pairDoc, eqDoc]
                         [[], [], [], pairParamDoc, eqParamDoc]))
               addNameHint eqTy (sUN "prf")
               elabDecl EAll toplevel elimDecl
               mapM_ elabPrim primitives
               -- Special case prim__believe_me because it doesn't work on just constants
               elabBelieveMe
               -- Finally, syntactic equality
               elabSynEq
    where elabPrim :: Prim -> Idris ()
          elabPrim (Prim n ty i def sc tot)
              = do updateContext (addOperator n ty i (valuePrim def))
                   setTotality n tot
                   i <- getIState
                   putIState i { idris_scprims = (n, sc) : idris_scprims i }

          valuePrim :: ([Const] -> Maybe Const) -> [Value] -> Maybe Value
          valuePrim prim vals = fmap VConstant (mapM getConst vals >>= prim)

          getConst (VConstant c) = Just c
          getConst _             = Nothing


          p_believeMe [_,_,x] = Just x
          p_believeMe _ = Nothing
          believeTy = Bind (sUN "a") (Pi (TType (UVar (-2))))
                       (Bind (sUN "b") (Pi (TType (UVar (-2))))
                         (Bind (sUN "x") (Pi (V 1)) (V 1)))
          elabBelieveMe
             = do let prim__believe_me = sUN "prim__believe_me"
                  updateContext (addOperator prim__believe_me believeTy 3 p_believeMe)
                  setTotality prim__believe_me (Partial NotCovering)
                  i <- getIState
                  putIState i {
                      idris_scprims = (prim__believe_me, (3, LNoOp)) : idris_scprims i
                    }

          p_synEq [t,_,x,y]
               | x == y = Just (VApp (VApp vnJust VErased)
                                (VApp (VApp vnRefl t) x))
               | otherwise = Just (VApp vnNothing VErased)
          p_synEq args = Nothing

          nMaybe = P (TCon 0 2) (sNS (sUN "Maybe") ["Maybe", "Prelude"]) Erased
          vnJust = VP (DCon 1 2) (sNS (sUN "Just") ["Maybe", "Prelude"]) VErased
          vnNothing = VP (DCon 0 1) (sNS (sUN "Nothing") ["Maybe", "Prelude"]) VErased
          vnRefl = VP (DCon 0 2) eqCon VErased

          synEqTy = Bind (sUN "a") (Pi (TType (UVar (-3))))
                     (Bind (sUN "b") (Pi (TType (UVar (-3))))
                      (Bind (sUN "x") (Pi (V 1))
                       (Bind (sUN "y") (Pi (V 1))
                         (mkApp nMaybe [mkApp (P (TCon 0 4) eqTy Erased)
                                               [V 3, V 2, V 1, V 0]]))))
          elabSynEq
             = do let synEq = sUN "prim__syntactic_eq"

                  updateContext (addOperator synEq synEqTy 4 p_synEq)
                  setTotality synEq (Total [])
                  i <- getIState
                  putIState i {
                     idris_scprims = (synEq, (4, LNoOp)) : idris_scprims i
                    }


-- | Elaborate a type provider
elabProvider :: ElabInfo -> SyntaxInfo -> FC -> ProvideWhat -> Name -> Idris ()
elabProvider info syn fc what n
    = do i <- getIState
         -- Ensure that the experimental extension is enabled
         unless (TypeProviders `elem` idris_language_extensions i) $
           ifail $ "Failed to define type provider \"" ++ show n ++
                   "\".\nYou must turn on the TypeProviders extension."

         ctxt <- getContext

         -- First elaborate the expected type (and check that it's a type)
         -- The goal type for a postulate is always Type.
         (ty', typ) <- case what of
                         ProvTerm ty p   -> elabVal toplevel False ty
                         ProvPostulate _ -> elabVal toplevel False PType
         unless (isTType typ) $
           ifail ("Expected a type, got " ++ show ty' ++ " : " ++ show typ)

         -- Elaborate the provider term to TT and check that the type matches
         (e, et) <- case what of
                      ProvTerm _ tm    -> elabVal toplevel False tm
                      ProvPostulate tm -> elabVal toplevel False tm
         unless (isProviderOf (normalise ctxt [] ty') et) $
           ifail $ "Expected provider type IO (Provider (" ++
                   show ty' ++ "))" ++ ", got " ++ show et ++ " instead."

         -- Execute the type provider and normalise the result
         -- use 'run__provider' to convert to a primitive IO action

         rhs <- execute (mkApp (P Ref (sUN "run__provider") Erased)
                                          [Erased, e])
         let rhs' = normalise ctxt [] rhs
         logLvl 3 $ "Normalised " ++ show n ++ "'s RHS to " ++ show rhs

         -- Extract the provided term or postulate from the type provider
         provided <- getProvided fc rhs'

         case provided of
           Provide tm
             | ProvTerm ty _ <- what ->
               do -- Finally add a top-level definition of the provided term
                  elabType info syn emptyDocstring [] fc [] n ty
                  elabClauses info fc [] n [PClause fc n (PApp fc (PRef fc n) []) [] (delab i tm) []]
                  logLvl 3 $ "Elaborated provider " ++ show n ++ " as: " ++ show tm
             | ProvPostulate _ <- what ->
               do -- Add the postulate
                  elabPostulate info syn (parseDocstring $ T.pack "Provided postulate") fc [] n (delab i tm)
                  logLvl 3 $ "Elaborated provided postulate " ++ show n
             | otherwise ->
               ierror . Msg $ "Attempted to provide a postulate where a term was expected."

    where isTType :: TT Name -> Bool
          isTType (TType _) = True
          isTType _ = False

          isProviderOf :: TT Name -> TT Name -> Bool
          isProviderOf tp prov
            | (P _ (UN io) _, [prov']) <- unApply prov
            , (P _ (NS (UN prov) [provs]) _, [tp']) <- unApply prov'
            , tp == tp', io == txt "IO"
            , prov == txt "Provider" && provs == txt "Providers" = True
          isProviderOf _ _ = False

elabTransform :: ElabInfo -> FC -> Bool -> PTerm -> PTerm -> Idris ()
elabTransform info fc safe lhs_in rhs_in
    = do ctxt <- getContext
         i <- getIState
         let lhs = addImplPat i lhs_in
         ((lhs', dlhs, []), _) <-
              tclift $ elaborate ctxt (sMN 0 "transLHS") infP []
                       (erun fc (buildTC i info True [] (sUN "transform")
                                   (infTerm lhs)))
         let lhs_tm = orderPats (getInferTerm lhs')
         let lhs_ty = getInferType lhs'
         let newargs = pvars i lhs_tm

         (clhs_tm, clhs_ty) <- recheckC fc [] lhs_tm
         logLvl 3 ("Transform LHS " ++ show clhs_tm)
         let rhs = addImplBound i (map fst newargs) rhs_in
         ((rhs', defer), _) <-
              tclift $ elaborate ctxt (sMN 0 "transRHS") clhs_ty []
                       (do pbinds i lhs_tm
                           setNextName
                           erun fc (build i info False [] (sUN "transform") rhs)
                           erun fc $ psolve lhs_tm
                           tt <- get_term
                           return (runState (collectDeferred Nothing tt) []))
         (crhs_tm, crhs_ty) <- recheckC fc [] rhs'
         logLvl 3 ("Transform RHS " ++ show crhs_tm)
         when safe $ case converts ctxt [] clhs_tm crhs_tm of
              OK _ -> return ()
              Error e -> ierror (At fc (CantUnify False clhs_tm crhs_tm e [] 0))
         addTrans (clhs_tm, crhs_tm)
         addIBC (IBCTrans (clhs_tm, crhs_tm))


elabRecord :: ElabInfo -> SyntaxInfo -> Docstring -> FC -> Name ->
              PTerm -> DataOpts -> Docstring -> Name -> PTerm -> Idris ()
elabRecord info syn doc fc tyn ty opts cdoc cn cty_in
    = do elabData info syn doc [] fc opts (PDatadecl tyn ty [(cdoc, [], cn, cty_in, fc, [])])
         -- TODO think: something more in info?
         cty' <- implicit info syn cn cty_in
         i <- getIState

         -- get bound implicits and propagate to setters (in case they
         -- provide useful information for inference)
         let extraImpls = getBoundImpls cty'

         cty <- case lookupTy cn (tt_ctxt i) of
                    [t] -> return (delab i t)
                    _ -> ifail "Something went inexplicably wrong"
         cimp <- case lookupCtxt cn (idris_implicits i) of
                    [imps] -> return imps
         let ptys = getProjs [] (renameBs cimp cty)
         let ptys_u = getProjs [] cty
         let recty = getRecTy cty

         -- rename indices when we generate the getter/setter types, so
         -- that they don't clash with the names of the projections
         -- we're generating
         let index_names_in = getRecNameMap "_in" recty
         let recty_in = substMatches index_names_in recty

         logLvl 1 $ show (recty, ptys)
         let substs = map (\ (n, _) -> (n, PApp fc (PRef fc n)
                                                [pexp (PRef fc rec)])) ptys

         -- Generate projection functions
         proj_decls <- mapM (mkProj recty_in substs cimp) (zip ptys [0..])
         logLvl 3 $ show proj_decls
         let nonImp = mapMaybe isNonImp (zip cimp ptys_u)
         let implBinds = getImplB id cty'

         -- Generate update functions
         update_decls <- mapM (mkUpdate recty index_names_in extraImpls
                                   (getFieldNames cty')
                                   implBinds (length nonImp)) (zip nonImp [0..])
         mapM_ (elabDecl EAll info) (concat proj_decls)
         logLvl 3 $ show update_decls
         mapM_ (tryElabDecl info) (update_decls)
  where
--     syn = syn_in { syn_namespace = show (nsroot tyn) : syn_namespace syn_in }

    isNonImp (PExp _ _ _ _, a) = Just a
    isNonImp _ = Nothing

    tryElabDecl info (fn, ty, val)
        = do i <- getIState
             idrisCatch (do elabDecl' EAll info ty
                            elabDecl' EAll info val)
                        (\v -> do iputStrLn $ show fc ++
                                      ":Warning - can't generate setter for " ++
                                      show fn ++ " (" ++ show ty ++ ")"
--                                       ++ "\n" ++ pshow i v
                                  putIState i)

    getBoundImpls (PPi (Imp _ _ _) n ty sc) = (n, ty) : getBoundImpls sc
    getBoundImpls _ = []

    getImplB k (PPi (Imp l s _) n Placeholder sc)
        = getImplB k sc
    getImplB k (PPi (Imp l s p) n ty sc)
        = getImplB (\x -> k (PPi (Imp l s p) n ty x)) sc
    getImplB k (PPi _ n ty sc)
        = getImplB k sc
    getImplB k _ = k

    renameBs (PImp _ _ _ _ _ : ps) (PPi p n ty s)
        = PPi p (mkImp n) ty (renameBs ps (substMatch n (PRef fc (mkImp n)) s))
    renameBs (_:ps) (PPi p n ty s) = PPi p n ty (renameBs ps s)
    renameBs _ t = t

    getProjs acc (PPi _ n ty s) = getProjs ((n, ty) : acc) s
    getProjs acc r = reverse acc

    getFieldNames (PPi (Exp _ _ _) n _ s) = n : getFieldNames s 
    getFieldNames (PPi _ _ _ s) = getFieldNames s
    getFieldNames _ = []

    getRecTy (PPi _ n ty s) = getRecTy s
    getRecTy t = t

    getRecNameMap x (PApp fc t args) = mapMaybe (toMN . getTm) args
      where
        toMN (PRef fc n) = Just (n, PRef fc (sMN 0 (show n ++ x)))
        toMN _ = Nothing
    getRecNameMap x _ = []

    rec = sMN 0 "rec"

    mkp (UN n) = sMN 0 ("p_" ++ str n)
    mkp (MN i n) = sMN i ("p_" ++ str n)
    mkp (NS n s) = NS (mkp n) s

    mkImp (UN n) = sUN ("implicit_" ++ str n)
    mkImp (MN i n) = sMN i ("implicit_" ++ str n)
    mkImp (NS n s) = NS (mkImp n) s

    mkType (UN n) = sUN ("set_" ++ str n)
    mkType (MN i n) = sMN i ("set_" ++ str n)
    mkType (NS n s) = NS (mkType n) s

    mkProj recty substs cimp ((pn_in, pty), pos)
        = do let pn = expandNS syn pn_in
             let pfnTy = PTy emptyDocstring [] defaultSyntax fc [] pn
                            (PPi expl rec recty
                               (substMatches substs pty))
             let pls = repeat Placeholder
             let before = pos
             let after = length substs - (pos + 1)
             let args = take before pls ++ PRef fc (mkp pn) : take after pls
             let iargs = map implicitise (zip cimp args)
             let lhs = PApp fc (PRef fc pn)
                        [pexp (PApp fc (PRef fc cn) iargs)]
             let rhs = PRef fc (mkp pn)
             let pclause = PClause fc pn lhs [] rhs []
             return [pfnTy, PClauses fc [] pn [pclause]]

    implicitise (pa, t) = pa { getTm = t }

    -- If the 'pty' we're updating includes anything in 'substs', we're
    -- updating the type as well, so use recty', otherwise just use
    -- recty
    mkUpdate recty inames extras fnames k num ((pn, pty), pos)
       = do let setname = expandNS syn $ mkType pn
            let valname = sMN 0 "updateval"
            let pn_out = sMN 0 (show pn ++ "_out")
            let pn_in = sMN 0 (show pn ++ "_in")
            let recty_in = substMatches [(pn, PRef fc pn_in)] recty
            let recty_out = substMatches [(pn, PRef fc pn_out)] recty
            let pt = substMatches inames $ 
                       k (implBindUp extras inames (PPi expl pn_out pty
                           (PPi expl rec recty_in recty_out)))
            let pfnTy = PTy emptyDocstring [] defaultSyntax fc [] setname pt
--             let pls = map (\x -> PRef fc (sMN x ("field" ++ show x))) [0..num-1]
            let inames_imp = map (\ (x,_) -> (x, Placeholder)) inames
            let pls = map (\x -> substMatches inames_imp (PRef fc x)) fnames
            let lhsArgs = pls
            let rhsArgs = take pos pls ++ (PRef fc valname) :
                               drop (pos + 1) pls
            let before = pos
            let pclause = PClause fc setname (PApp fc (PRef fc setname)
                                              [pexp (PRef fc valname),
                                               pexp (PApp fc (PRef fc cn)
                                                        (map pexp lhsArgs))])
                                             []
                                             (PApp fc (PRef fc cn)
                                                      (map pexp rhsArgs)) []
            return (pn, pfnTy, PClauses fc [] setname [pclause])

    implBindUp [] is t = t
    implBindUp ((n, ty):ns) is t 
         = let n' = case lookup n is of
                         Just (PRef _ x) -> x
                         _ -> n in
               if n `elem` allNamesIn t 
                  then PPi impl n' ty (implBindUp ns is t)
                  else implBindUp ns is t

-- FIXME: 'forcenames' is an almighty hack! Need a better way of
-- erasing non-forceable things
-- ^^^
-- TODO: the above is a comment from the past;
-- forcenames is probably no longer needed
elabCon :: ElabInfo -> SyntaxInfo -> Name -> Bool ->
           (Docstring, [(Name, Docstring)], Name, PTerm, FC, [Name]) -> Idris (Name, Type)
elabCon info syn tn codata (doc, argDocs, n, t_in, fc, forcenames)
    = do checkUndefined fc n
         ctxt <- getContext
         i <- getIState
         t_in <- implicit info syn n (if codata then mkLazy t_in else t_in)
         let t = addImpl i t_in
         logLvl 2 $ show fc ++ ":Constructor " ++ show n ++ " : " ++ show t
         let inacc = inaccessibleArgs 0 t
         logLvl 5 $ "Inaccessible args: " ++ show inacc
         ((t', defer, is), log) <-
              tclift $ elaborate ctxt n (TType (UVal 0)) []
                       (errAt "constructor " n (erun fc (build i info False [] n t)))
         logLvl 2 $ "Rechecking " ++ show t'
         def' <- checkDef fc defer
         let def'' = map (\(n, (i, top, t)) -> (n, (i, top, t, True))) def'
         addDeferred def''
         mapM_ (\(n, _) -> addIBC (IBCDef n)) def''

         mapM_ (elabCaseBlock info []) is
         ctxt <- getContext
         (cty, _)  <- recheckC fc [] t'
         let cty' = normaliseC ctxt [] cty
         tyIs cty'
         logLvl 2 $ "---> " ++ show n ++ " : " ++ show cty'
         addIBC (IBCDef n)
         checkDocs fc argDocs t_in
         addDocStr n doc argDocs
         addIBC (IBCDoc n)
         fputState (opt_inaccessible . ist_optimisation n) inacc
         addIBC (IBCOpt n)
         return (n, cty')
  where
    tyIs (Bind n b sc) = tyIs sc
    tyIs t | (P _ n' _, _) <- unApply t
        = if n' /= tn then tclift $ tfail (At fc (Msg (show n' ++ " is not " ++ show tn)))
             else return ()
    tyIs t = tclift $ tfail (At fc (Msg (show t ++ " is not " ++ show tn)))

    mkLazy (PPi pl n ty sc) 
        = let ty' = if getTyName ty
                       then PApp fc (PRef fc (sUN "Lazy'"))
                            [pexp (PRef fc (sUN "LazyCodata")),
                             pexp ty]
                       else ty in
              PPi pl n ty' (mkLazy sc)
    mkLazy t = t

    getTyName (PApp _ (PRef _ n) _) = n == nsroot tn
    getTyName (PRef _ n) = n == nsroot tn
    getTyName _ = False


    getNamePos :: Int -> PTerm -> Name -> Maybe Int
    getNamePos i (PPi _ n _ sc) x | n == x = Just i
                                  | otherwise = getNamePos (i + 1) sc x
    getNamePos _ _ _ = Nothing

-- | Elaborate a collection of left-hand and right-hand pairs - that is, a
-- top-level definition.
elabClauses :: ElabInfo -> FC -> FnOpts -> Name -> [PClause] -> Idris ()
elabClauses info fc opts n_in cs = let n = liftname info n_in in
      do ctxt <- getContext
         ist  <- getIState
         inacc <- map fst <$> fgetState (opt_inaccessible . ist_optimisation n)

         -- Check n actually exists, with no definition yet
         let tys = lookupTy n ctxt
         let reflect = Reflection `elem` opts
         checkUndefined n ctxt
         unless (length tys > 1) $ do
           fty <- case tys of
              [] -> -- TODO: turn into a CAF if there's no arguments
                    -- question: CAFs in where blocks?
                    tclift $ tfail $ At fc (NoTypeDecl n)
              [ty] -> return ty
           let atys = map snd (getArgTys fty)
           cs_elab <- mapM (elabClause info opts)
                           (zip [0..] cs)
           let (pats_in, cs_full) = unzip cs_elab

           logLvl 3 $ "Elaborated patterns:\n" ++ show pats_in

           solveDeferred n

           -- just ensure that the structure exists
           fmodifyState (ist_optimisation n) id
           addIBC (IBCOpt n)

           ist <- getIState
           let pats = map (simple_lhs (tt_ctxt ist)) $ doTransforms ist pats_in

  --          logLvl 3 (showSep "\n" (map (\ (l,r) ->
  --                                         show l ++ " = " ++
  --                                         show r) pats))
           let tcase = opt_typecase (idris_options ist)

           -- Summary of what's about to happen: Definitions go:
           --
           -- pats_in -> pats -> pdef -> pdef'

           -- addCaseDef builds case trees from <pdef> and <pdef'>

           -- pdef is the compile-time pattern definition.
           -- This will get further optimised for run-time, and, separately,
           -- further inlined to help with totality checking.
           let pdef = map debind pats

           logLvl 5 $ "Initial typechecked patterns:\n" ++ show pats
           logLvl 5 $ "Initial typechecked pattern def:\n" ++ show pdef

           -- Look for 'static' names and generate new specialised
           -- definitions for them

           mapM_ (\ e -> case e of
                           Left _ -> return ()
                           Right (l, r) -> elabPE info fc n r) pats

           -- NOTE: Need to store original definition so that proofs which
           -- rely on its structure aren't affected by any changes to the
           -- inliner. Just use the inlined version to generate pdef' and to
           -- help with later inlinings.

           ist <- getIState
           let pdef_inl = inlineDef ist pdef

           numArgs <- tclift $ sameLength pdef

           case specNames opts of
                Just _ -> logLvl 5 $ "Partially evaluated:\n" ++ show pats
                _ -> return ()

           erInfo <- getErasureInfo <$> getIState
           tree@(CaseDef scargs sc _) <- tclift $
                   simpleCase tcase False reflect CompileTime fc inacc atys pdef erInfo
           cov <- coverage
           pmissing <-
                   if cov && not (hasDefault cs)
                      then do missing <- genClauses fc n (map getLHS pdef) cs_full
                              -- missing <- genMissing n scargs sc
                              missing' <- filterM (checkPossible info fc True n) missing
                              let clhs = map getLHS pdef
                              logLvl 2 $ "Must be unreachable:\n" ++
                                          showSep "\n" (map showTmImpls missing') ++
                                         "\nAgainst: " ++
                                          showSep "\n" (map (\t -> showTmImpls (delab ist t)) (map getLHS pdef))
                              -- filter out anything in missing' which is
                              -- matched by any of clhs. This might happen since
                              -- unification may force a variable to take a
                              -- particular form, rather than force a case
                              -- to be impossible.
                              return (filter (noMatch ist clhs) missing')
                      else return []
           let pcover = null pmissing

           -- pdef' is the version that gets compiled for run-time
           pdef_in' <- applyOpts pdef
           let pdef' = map (simple_rt (tt_ctxt ist)) pdef_in'

           logLvl 5 $ "After data structure transformations:\n" ++ show pdef'

           ist <- getIState
  --          let wf = wellFounded ist n sc
           let tot = if pcover || AssertTotal `elem` opts
                      then Unchecked -- finish checking later
                      else Partial NotCovering -- already know it's not total

  --          case lookupCtxt (namespace info) n (idris_flags ist) of
  --             [fs] -> if TotalFn `elem` fs
  --                       then case tot of
  --                               Total _ -> return ()
  --                               t -> tclift $ tfail (At fc (Msg (show n ++ " is " ++ show t)))
  --                       else return ()
  --             _ -> return ()
           case tree of
               CaseDef _ _ [] -> return ()
               CaseDef _ _ xs -> mapM_ (\x ->
                   iputStrLn $ show fc ++
                                ":warning - Unreachable case: " ++
                                   show (delab ist x)) xs
           let knowncovering = (pcover && cov) || AssertTotal `elem` opts

           tree' <- tclift $ simpleCase tcase knowncovering reflect
                                        RunTime fc inacc atys pdef' erInfo
           logLvl 3 $ "Unoptimised " ++ show n ++ ": " ++ show tree
           logLvl 3 $ "Optimised: " ++ show tree'
           ctxt <- getContext
           ist <- getIState
           let opt = idris_optimisation ist
           putIState (ist { idris_patdefs = addDef n (force pdef', force pmissing)
                                                (idris_patdefs ist) })
           let caseInfo = CaseInfo (inlinable opts) (dictionary opts)
           case lookupTy n ctxt of
               [ty] -> do updateContext (addCasedef n erInfo caseInfo
                                                       tcase knowncovering
                                                       reflect
                                                       (AssertTotal `elem` opts)
                                                       atys
                                                       inacc
                                                       pats
                                                       pdef pdef pdef_inl pdef' ty)
                          addIBC (IBCDef n)
                          setTotality n tot
                          when (not reflect) $ do totcheck (fc, n)
                                                  defer_totcheck (fc, n)
                          when (tot /= Unchecked) $ addIBC (IBCTotal n tot)
                          i <- getIState
                          case lookupDef n (tt_ctxt i) of
                              (CaseOp _ _ _ _ _ cd : _) ->
                                let (scargs, sc) = cases_compiletime cd
                                    (scargs', sc') = cases_runtime cd in
                                  do let calls = findCalls sc' scargs'
                                     let used = findUsedArgs sc' scargs'
                                     -- let scg = buildSCG i sc scargs
                                     -- add SCG later, when checking totality
                                     let cg = CGInfo scargs' calls [] used []  -- TODO: remove this, not needed anymore
                                     logLvl 2 $ "Called names: " ++ show cg
                                     addToCG n cg
                                     addToCalledG n (nub (map fst calls)) -- plus names in type!
                                     addIBC (IBCCG n)
                              _ -> return ()
                          return ()
  --                         addIBC (IBCTotal n tot)
               [] -> return ()
           -- Check it's covering, if 'covering' option is used. Chase
           -- all called functions, and fail if any of them are also
           -- 'Partial NotCovering'
           when (CoveringFn `elem` opts) $ checkAllCovering fc [] n n
  where
    noMatch i cs tm = all (\x -> case matchClause i (delab' i x True True) tm of
                                      Right _ -> False
                                      Left miss -> True) cs

    checkUndefined n ctxt = case lookupDef n ctxt of
                                 [] -> return ()
                                 [TyDecl _ _] -> return ()
                                 _ -> tclift $ tfail (At fc (AlreadyDefined n))

    debind (Right (x, y)) = let (vs, x') = depat [] x
                                (_, y') = depat [] y in
                                (vs, x', y')
    debind (Left x)       = let (vs, x') = depat [] x in
                                (vs, x', Impossible)

    depat acc (Bind n (PVar t) sc) = depat (n : acc) (instantiate (P Bound n t) sc)
    depat acc x = (acc, x)

    hasDefault cs | (PClause _ _ last _ _ _ :_) <- reverse cs
                  , (PApp fn s args) <- last = all ((==Placeholder) . getTm) args
    hasDefault _ = False

    getLHS (_, l, _) = l

    simple_lhs ctxt (Right (x, y)) = Right (normalise ctxt [] x, 
                                            force (normalisePats ctxt [] y))
    simple_lhs ctxt t = t

    simple_rt ctxt (p, x, y) = (p, x, force (uniqueBinders p 
                                                (rt_simplify ctxt [] y)))

    -- this is so pattern types are in the right form for erasure
    normalisePats ctxt env (Bind n (PVar t) sc) 
       = let t' = normalise ctxt env t in
             Bind n (PVar t') (normalisePats ctxt ((n, PVar t') : env) sc)
    normalisePats ctxt env (Bind n (PVTy t) sc) 
       = let t' = normalise ctxt env t in
             Bind n (PVTy t') (normalisePats ctxt ((n, PVar t') : env) sc)
    normalisePats ctxt env t = t

    specNames [] = Nothing
    specNames (Specialise ns : _) = Just ns
    specNames (_ : xs) = specNames xs

    sameLength ((_, x, _) : xs)
        = do l <- sameLength xs
             let (f, as) = unApply x
             if (null xs || l == length as) then return (length as)
                else tfail (At fc (Msg "Clauses have differing numbers of arguments "))
    sameLength [] = return 0

    -- apply all transformations (just specialisation for now, add
    -- user defined transformation rules later)
    doTransforms ist pats =
           case specNames opts of
                Nothing -> pats
                Just ns -> partial_eval (tt_ctxt ist) ns pats

-- Find 'static' applications in a term and partially evaluate them
elabPE :: ElabInfo -> FC -> Name -> Term -> Idris ()
elabPE info fc caller r =
  do ist <- getIState
     let sa = getSpecApps ist [] r
     mapM_ (mkSpecialised ist) sa
  where 
    -- TODO: Add a PTerm level transformation rule, which is basically the 
    -- new definition in reverse (before specialising it). 
    -- RHS => LHS where implicit arguments are left blank in the 
    -- transformation.

    -- Apply that transformation after every PClauses elaboration

    mkSpecialised ist specapp_in = do
        let (specTy, specapp) = getSpecTy ist specapp_in
        let (n, newnm, pats) = getSpecClause ist specapp
        let undef = case lookupDef newnm (tt_ctxt ist) of
                         [] -> True
                         _ -> False
        logLvl 5 $ show (newnm, map (concreteArg ist) (snd specapp))
        idrisCatch
          (when (undef && all (concreteArg ist) (snd specapp)) $ do
            cgns <- getAllNames n
            let opts = [Specialise (map (\x -> (x, Nothing)) cgns ++ 
                                     mapMaybe specName (snd specapp))]
            logLvl 3 $ "Specialising application: " ++ show specapp
            logLvl 2 $ "New name: " ++ show newnm
            iLOG $ "PE definition type : " ++ (show specTy)
                        ++ "\n" ++ show opts
            logLvl 2 $ "PE definition " ++ show newnm ++ ":\n" ++
                        showSep "\n" 
                           (map (\ (lhs, rhs) ->
                              (showTmImpls lhs ++ " = " ++ 
                               showTmImpls rhs)) pats)
            elabType info defaultSyntax emptyDocstring [] fc opts newnm specTy
            let def = map (\ (lhs, rhs) -> PClause fc newnm lhs [] rhs []) pats
            elabClauses info fc opts newnm def
            logLvl 2 $ "Specialised " ++ show newnm)
          -- if it doesn't work, just don't specialise. Could happen for lots
          -- of valid reasons (e.g. local variables in scope which can't be
          -- lifted out).
          (\e -> logLvl 4 $ "Couldn't specialise: " ++ (pshow ist e)) 

    specName (ImplicitS, tm) 
        | (P Ref n _, _) <- unApply tm = Just (n, Just 1)
    specName (ExplicitS, tm)
        | (P Ref n _, _) <- unApply tm = Just (n, Just 1)
    specName _ = Nothing

    concreteArg ist (ImplicitS, tm) = concreteTm ist tm
    concreteArg ist (ExplicitS, tm) = concreteTm ist tm
    concreteArg ist _ = True

    concreteTm ist tm | (P _ n _, _) <- unApply tm =
        case lookupTy n (tt_ctxt ist) of
             [] -> False
             _ -> True
    concreteTm ist (Constant _) = True
    concreteTm ist _ = False

    -- get the type of a specialised application
    getSpecTy ist (n, args)
       = case lookupTy n (tt_ctxt ist) of
              [ty] -> let (specty_in, args') = specType args (explicitNames ty)
                          specty = normalise (tt_ctxt ist) [] (finalise specty_in)
                          t = mkPE_TyDecl ist args' (explicitNames specty) in
                          (t, (n, args'))
--                             (normalise (tt_ctxt ist) [] (specType args ty))
              _ -> error "Can't happen (getSpecTy)"

    getSpecClause ist (n, args)
       = let newnm = sUN ("__"++show (nsroot n) ++ "_" ++ 
                               showSep "_" (map showArg args)) in 
                               -- UN (show n ++ show (map snd args)) in
             (n, newnm, mkPE_TermDecl ist newnm n args)
      where showArg (ExplicitS, n) = show n
            showArg (ImplicitS, n) = show n
            showArg _ = ""


-- Elaborate a value, returning any new bindings created (this will only
-- happen if elaborating as a pattern clause)
elabValBind :: ElabInfo -> Bool -> Bool -> PTerm -> Idris (Term, Type, [(Name, Type)])
elabValBind info aspat norm tm_in
   = do ctxt <- getContext
        i <- getIState
        let tm = addImpl i tm_in
        logLvl 10 (showTmImpls tm)
        -- try:
        --    * ordinary elaboration
        --    * elaboration as a Type
        --    * elaboration as a function a -> b

        ((tm', defer, is), _) <-
--             tctry (elaborate ctxt (MN 0 "val") (TType (UVal 0)) []
--                        (build i info aspat (MN 0 "val") tm))
                tclift (elaborate ctxt (sMN 0 "val") infP []
                        (build i info aspat [Reflection] (sMN 0 "val") (infTerm tm)))
        let vtm = orderPats (getInferTerm tm')

        def' <- checkDef (fileFC "(input)") defer
        let def'' = map (\(n, (i, top, t)) -> (n, (i, top, t, True))) def'
        addDeferred def''
        mapM_ (elabCaseBlock info []) is

        logLvl 3 ("Value: " ++ show vtm)
--         recheckC (fileFC "(input)") [] tm'
--         logLvl 2 (show vtm)
        (vtm_in, vty) <- recheckC (fileFC "(input)") [] vtm

        let vtm = if norm then normalise (tt_ctxt i) [] vtm_in
                          else vtm_in
        let bargs = getPBtys vtm

        return (vtm, vty, bargs)

elabVal :: ElabInfo -> Bool -> PTerm -> Idris (Term, Type)
elabVal info aspat tm_in
   = do (tm, ty, _) <- elabValBind info aspat False tm_in
        return (tm, ty)

-- checks if the clause is a possible left hand side. Returns the term if
-- possible, otherwise Nothing.

checkPossible :: ElabInfo -> FC -> Bool -> Name -> PTerm -> Idris Bool
checkPossible info fc tcgen fname lhs_in
   = do ctxt <- getContext
        i <- getIState
        let lhs = addImplPat i lhs_in
        -- if the LHS type checks, it is possible
        case elaborate ctxt (sMN 0 "patLHS") infP []
                            (erun fc (buildTC i info True [] fname (infTerm lhs))) of
            OK ((lhs', _, _), _) ->
               do let lhs_tm = orderPats (getInferTerm lhs')
                  case recheck ctxt [] (forget lhs_tm) lhs_tm of
                       OK _ -> return True
                       err -> return False
            -- if it's a recoverable error, the case may become possible
            Error err -> if tcgen then return (recoverable ctxt err)
                                  else return (validCase ctxt err ||
                                                 recoverable ctxt err)
    where validCase ctxt (CantUnify _ topx topy e _ _)
              = let topx' = normalise ctxt [] topx
                    topy' = normalise ctxt [] topy in
                    not (sameFam topx' topy' || not (validCase ctxt e))
          validCase ctxt (CantConvert _ _ _) = False
          validCase ctxt (At _ e) = validCase ctxt e
          validCase ctxt (Elaborating _ _ e) = validCase ctxt e
          validCase ctxt (ElaboratingArg _ _ _ e) = validCase ctxt e
          validCase ctxt _ = True
           
          recoverable ctxt (CantUnify r topx topy e _ _) 
              = let topx' = normalise ctxt [] topx
                    topy' = normalise ctxt [] topy in
                    checkRec topx' topy'
          recoverable ctxt (At _ e) = recoverable ctxt e
          recoverable ctxt (Elaborating _ _ e) = recoverable ctxt e
          recoverable ctxt (ElaboratingArg _ _ _ e) = recoverable ctxt e
          recoverable _ _ = False

          sameFam topx topy 
              = case (unApply topx, unApply topy) of
                     ((P _ x _, _), (P _ y _, _)) -> x == y
                     _ -> False

          -- different notion of recoverable than in unification, since we
          -- have no metavars -- just looking to see if a constructor is failing
          -- to unify with a function that may be reduced later

          checkRec (App f a) p@(P _ _ _) = checkRec f p
          checkRec p@(P _ _ _) (App f a) = checkRec p f
          checkRec fa@(App _ _) fa'@(App _ _) 
              | (f, as) <- unApply fa,
                (f', as') <- unApply fa'
                   = if (length as /= length as') 
                        then checkRec f f' 
                        else checkRec f f' && and (zipWith checkRec as as')
          checkRec (P xt x _) (P yt y _) = x == y || ntRec xt yt
          checkRec _ _ = False

          ntRec x y | Ref <- x = True
                    | Ref <- y = True
                    | otherwise = False -- name is different, unrecoverable

getFixedInType i env (PExp _ _ _ _ : is) (Bind n (Pi t) sc)
    = getFixedInType i (n : env) is (instantiate (P Bound n t) sc)
getFixedInType i env (_ : is) (Bind n (Pi t) sc)
    = getFixedInType i (n : env) is (instantiate (P Bound n t) sc)
getFixedInType i env is tm@(App f a)
    | (P _ tn _, args) <- unApply tm
       = case lookupCtxt tn (idris_datatypes i) of
            [t] -> nub $ paramNames args env (param_pos t) ++
                         getFixedInType i env is f ++
                         getFixedInType i env is a
            [] -> nub $ getFixedInType i env is f ++
                        getFixedInType i env is a
    | otherwise = nub $ getFixedInType i env is f ++
                        getFixedInType i env is a
getFixedInType i _ _ _ = []

getFlexInType i env ps (Bind n (Pi t) sc)
    = nub $ (if (not (n `elem` ps)) then getFlexInType i env ps t else []) ++
            getFlexInType i (n : env) ps (instantiate (P Bound n t) sc)
getFlexInType i env ps tm@(App f a)
    | (P _ tn _, args) <- unApply tm
       = case lookupCtxt tn (idris_datatypes i) of
            [t] -> nub $ paramNames args env [x | x <- [0..length args],
                                                  not (x `elem` param_pos t)] 
                          ++ getFlexInType i env ps f ++
                             getFlexInType i env ps a
            [] -> nub $ getFlexInType i env ps f ++
                        getFlexInType i env ps a
    | otherwise = nub $ getFlexInType i env ps f ++
                        getFlexInType i env ps a
getFlexInType i _ _ _ = []

-- Treat a name as a parameter if it appears in parameter positions in
-- types, and never in a non-parameter position in a (non-param) argument type.

getParamsInType i env ps t = let fix = getFixedInType i env ps t
                                 flex = getFlexInType i env fix t in
                                 [x | x <- fix, not (x `elem` flex)]

paramNames args env [] = []
paramNames args env (p : ps)
   | length args > p = case args!!p of
                          P _ n _ -> if n `elem` env
                                        then n : paramNames args env ps
                                        else paramNames args env ps
                          _ -> paramNames args env ps
   | otherwise = paramNames args env ps

propagateParams :: [Name] -> Type -> PTerm -> PTerm
propagateParams ps t tm@(PApp _ (PRef fc n) args)
     = PApp fc (PRef fc n) (addP t args)
   where addP (Bind n _ sc) (t : ts)
              | Placeholder <- getTm t,
                n `elem` ps,
                not (n `elem` allNamesIn tm)
                    = t { getTm = PRef fc n } : addP sc ts
         addP (Bind n _ sc) (t : ts) = t : addP sc ts
         addP _ ts = ts
propagateParams ps t (PRef fc n)
     = PApp fc (PRef fc n) (map (\x -> pimp x (PRef fc x) True) ps)
propagateParams ps t x = x

-- Return the elaborated LHS/RHS, and the original LHS with implicits added
elabClause :: ElabInfo -> FnOpts -> (Int, PClause) ->
              Idris (Either Term (Term, Term), PTerm)
elabClause info opts (_, PClause fc fname lhs_in [] PImpossible [])
   = do let tcgen = Dictionary `elem` opts
        i <- get
        let lhs = addImpl i lhs_in
        b <- checkPossible info fc tcgen fname lhs_in
        case b of
            True -> tclift $ tfail (At fc 
                                (Msg $ show lhs_in ++ " is a valid case"))
            False -> do ptm <- mkPatTm lhs_in
                        return (Left ptm, lhs)
elabClause info opts (cnum, PClause fc fname lhs_in withs rhs_in whereblock)
   = do let tcgen = Dictionary `elem` opts
        ctxt <- getContext

        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        i <- getIState
        inf <- isTyInferred fname
        -- get the parameters first, to pass through to any where block
        let fn_ty = case lookupTy fname (tt_ctxt i) of
                         [t] -> t
                         _ -> error "Can't happen (elabClause function type)"
        let fn_is = case lookupCtxt fname (idris_implicits i) of
                         [t] -> t
                         _ -> []
        let params = getParamsInType i [] fn_is fn_ty
        let lhs = mkLHSapp $ stripUnmatchable i $
                    propagateParams params fn_ty (addImplPat i (stripLinear i lhs_in))
        logLvl 5 ("LHS: " ++ show fc ++ " " ++ showTmImpls lhs)
        logLvl 4 ("Fixed parameters: " ++ show params ++ " from " ++ show lhs_in ++
                  "\n" ++ show (fn_ty, fn_is))

        (((lhs', dlhs, []), probs, inj), _) <-
            tclift $ elaborate ctxt (sMN 0 "patLHS") infP []
                     (do res <- errAt "left hand side of " fname
                                  (erun fc (buildTC i info True opts fname (infTerm lhs)))
                         probs <- get_probs
                         inj <- get_inj
                         return (res, probs, inj))

        when inf $ addTyInfConstraints fc (map (\(x,y,_,_,_,_) -> (x,y)) probs)

        let lhs_tm = orderPats (getInferTerm lhs')
        let lhs_ty = getInferType lhs'
        logLvl 3 ("Elaborated: " ++ show lhs_tm)
        logLvl 3 ("Elaborated type: " ++ show lhs_ty)
        logLvl 5 ("Injective: " ++ show fname ++ " " ++ show inj)

        -- If we're inferring metavariables in the type, don't recheck,
        -- because we're only doing this to try to work out those metavariables
        (clhs_c, clhsty) <- if not inf
                               then recheckC fc [] lhs_tm
                               else return (lhs_tm, lhs_ty)
        let clhs = normalise ctxt [] clhs_c
        
        logLvl 3 ("Normalised LHS: " ++ showTmImpls (delabMV i clhs))

        rep <- useREPL
        when rep $ do
          addInternalApp (fc_fname fc) (fst . fc_start $ fc) (delabMV i clhs) -- TODO: Should use span instead of line and filename?
          addIBC (IBCLineApp (fc_fname fc) (fst . fc_start $ fc) (delabMV i clhs))

        logLvl 5 ("Checked " ++ show clhs ++ "\n" ++ show clhsty)
        -- Elaborate where block
        ist <- getIState
        windex <- getName
        let decls = nub (concatMap declared whereblock)
        let defs = nub (decls ++ concatMap defined whereblock)
        let newargs = pvars ist lhs_tm
        let winfo = pinfo info newargs defs windex
        let wb = map (expandParamsD False ist decorate newargs defs) whereblock

        -- Split the where block into declarations with a type, and those
        -- without
        -- Elaborate those with a type *before* RHS, those without *after*
        let (wbefore, wafter) = sepBlocks wb

        logLvl 2 $ "Where block:\n " ++ show wbefore ++ "\n" ++ show wafter
        mapM_ (elabDecl' EAll winfo) wbefore
        -- Now build the RHS, using the type of the LHS as the goal.
        i <- getIState -- new implicits from where block
        logLvl 5 (showTmImpls (expandParams decorate newargs defs (defs \\ decls) rhs_in))
        let rhs = addImplBoundInf i (map fst newargs) (defs \\ decls)
                                 (expandParams decorate newargs defs (defs \\ decls) rhs_in)
        logLvl 2 $ "RHS: " ++ showTmImpls rhs
        ctxt <- getContext -- new context with where block added
        logLvl 5 "STARTING CHECK"
        ((rhs', defer, is, probs), _) <-
           tclift $ elaborate ctxt (sMN 0 "patRHS") clhsty []
                    (do pbinds ist lhs_tm
                        mapM_ setinj (nub (params ++ inj))
                        setNextName 
                        (_, _, is) <- errAt "right hand side of " fname
                                         (erun fc (build i winfo False opts fname rhs))
                        errAt "right hand side of " fname
                              (erun fc $ psolve lhs_tm)
                        hs <- get_holes
                        aux <- getAux
                        mapM_ (elabCaseHole aux) hs
                        tt <- get_term
                        let (tm, ds) = runState (collectDeferred (Just fname) tt) []
                        probs <- get_probs
                        return (tm, ds, is, probs))

        when inf $ addTyInfConstraints fc (map (\(x,y,_,_,_,_) -> (x,y)) probs)

        logLvl 5 "DONE CHECK"
        logLvl 2 $ "---> " ++ show rhs'
        when (not (null defer)) $ iLOG $ "DEFERRED " ++ 
                    show (map (\ (n, (_,_,t)) -> (n, t)) defer)
        def' <- checkDef fc defer
        let def'' = map (\(n, (i, top, t)) -> (n, (i, top, t, False))) def'
        addDeferred def''
        mapM_ (\(n, _) -> addIBC (IBCDef n)) def''

        when (not (null def')) $ do
           mapM_ defer_totcheck (map (\x -> (fc, fst x)) def'')

        -- Now the remaining deferred (i.e. no type declarations) clauses
        -- from the where block

        mapM_ (elabDecl' EAll winfo) wafter
        mapM_ (elabCaseBlock winfo opts) is

        ctxt <- getContext
        logLvl 5 $ "Rechecking"
        logLvl 6 $ " ==> " ++ show (forget rhs')
        (crhs, crhsty) <- if not inf 
                             then recheckC fc [] rhs'
                             else return (rhs', clhsty)
        logLvl 6 $ " ==> " ++ show crhsty ++ "   against   " ++ show clhsty
        case  converts ctxt [] clhsty crhsty of
            OK _ -> return ()
            Error e -> ierror (At fc (CantUnify False clhsty crhsty e [] 0))
        i <- getIState
        checkInferred fc (delab' i crhs True True) rhs
        -- if the function is declared '%error_reverse', or its type,
        -- then we'll try running it in reverse to improve error messages
        let (ret_fam, _) = unApply (getRetTy crhsty)
        rev <- case ret_fam of
                    P _ rfamn _ -> 
                        case lookupCtxt rfamn (idris_datatypes i) of
                             [TI _ _ dopts _ _] -> 
                                 return (DataErrRev `elem` dopts)
                             _ -> return False
                    _ -> return False

        when (rev || ErrorReverse `elem` opts) $ do
           addIBC (IBCErrRev (crhs, clhs))
           addErrRev (crhs, clhs) 
        return $ (Right (clhs, crhs), lhs)
  where
    pinfo :: ElabInfo -> [(Name, PTerm)] -> [Name] -> Int -> ElabInfo
    pinfo info ns ds i
          = let newps = params info ++ ns
                dsParams = map (\n -> (n, map fst newps)) ds
                newb = addAlist dsParams (inblock info)
                l = liftname info in
                info { params = newps,
                       inblock = newb,
                       liftname = id -- (\n -> case lookupCtxt n newb of
                                     --      Nothing -> n
                                     --      _ -> MN i (show n)) . l
                     }

    mkLHSapp t@(PRef _ _) = trace ("APP " ++ show t) $ PApp fc t []
    mkLHSapp t = t

    decorate (NS x ns)
       = NS (SN (WhereN cnum fname x)) ns -- ++ [show cnum])
--        = NS (UN ('#':show x)) (ns ++ [show cnum, show fname])
    decorate x
       = SN (WhereN cnum fname x)
--        = NS (SN (WhereN cnum fname x)) [show cnum]
--        = NS (UN ('#':show x)) [show cnum, show fname]

    sepBlocks bs = sepBlocks' [] bs where
      sepBlocks' ns (d@(PTy _ _ _ _ _ n t) : bs)
            = let (bf, af) = sepBlocks' (n : ns) bs in
                  (d : bf, af)
      sepBlocks' ns (d@(PClauses _ _ n _) : bs)
         | not (n `elem` ns) = let (bf, af) = sepBlocks' ns bs in
                                   (bf, d : af)
      sepBlocks' ns (b : bs) = let (bf, af) = sepBlocks' ns bs in
                                   (b : bf, af)
      sepBlocks' ns [] = ([], [])


    -- if a hole is just an argument/result of a case block, treat it as
    -- the unit type. Hack to help elaborate case in do blocks.
    elabCaseHole aux h = do
        focus h
        g <- goal
        case g of
             TType _ -> when (any (isArg h) aux) $ do apply (Var unitTy) []; solve
             _ -> return ()

    -- Is the name a pattern argument in the declaration
    isArg :: Name -> PDecl -> Bool
    isArg n (PClauses _ _ _ cs) = any isArg' cs
      where
        isArg' (PClause _ _ (PApp _ _ args) _ _ _) 
           = any (\x -> case x of
                          PRef _ n' -> n == n'
                          _ -> False) (map getTm args)
        isArg' _ = False
    isArg _ _ = False

elabClause info opts (_, PWith fc fname lhs_in withs wval_in withblock)
   = do let tcgen = Dictionary `elem` opts
        ctxt <- getContext
        -- Build the LHS as an "Infer", and pull out its type and
        -- pattern bindings
        i <- getIState
        -- get the parameters first, to pass through to any where block
        let fn_ty = case lookupTy fname (tt_ctxt i) of
                         [t] -> t
                         _ -> error "Can't happen (elabClause function type)"
        let fn_is = case lookupCtxt fname (idris_implicits i) of
                         [t] -> t
                         _ -> []
        let params = getParamsInType i [] fn_is fn_ty
        let lhs = propagateParams params fn_ty (addImplPat i (stripLinear i lhs_in))
        logLvl 2 ("LHS: " ++ show lhs)
        ((lhs', dlhs, []), _) <-
            tclift $ elaborate ctxt (sMN 0 "patLHS") infP []
              (errAt "left hand side of with in " fname
                (erun fc (buildTC i info True opts fname (infTerm lhs))) )
        let lhs_tm = orderPats (getInferTerm lhs')
        let lhs_ty = getInferType lhs'
        let ret_ty = getRetTy lhs_ty
        logLvl 3 (show lhs_tm)
        (clhs, clhsty) <- recheckC fc [] lhs_tm
        logLvl 5 ("Checked " ++ show clhs)
        let bargs = getPBtys lhs_tm
        let wval = addImplBound i (map fst bargs) wval_in
        logLvl 5 ("Checking " ++ showTmImpls wval)
        -- Elaborate wval in this context
        ((wval', defer, is), _) <-
            tclift $ elaborate ctxt (sMN 0 "withRHS")
                        (bindTyArgs PVTy bargs infP) []
                        (do pbinds i lhs_tm
                            setNextName
                            -- TODO: may want where here - see winfo abpve
                            (_', d, is) <- errAt "with value in " fname
                              (erun fc (build i info False opts fname (infTerm wval)))
                            erun fc $ psolve lhs_tm
                            tt <- get_term
                            return (tt, d, is))
        def' <- checkDef fc defer
        let def'' = map (\(n, (i, top, t)) -> (n, (i, top, t, False))) def'
        addDeferred def''
        mapM_ (elabCaseBlock info opts) is
        logLvl 5 ("Checked wval " ++ show wval')
        (cwval, cwvalty) <- recheckC fc [] (getInferTerm wval')
        let cwvaltyN = explicitNames cwvalty
        let cwvalN = explicitNames cwval
        logLvl 5 ("With type " ++ show cwvalty ++ "\nRet type " ++ show ret_ty)
        let pvars = map fst (getPBtys cwvalty)
        -- we need the unelaborated term to get the names it depends on
        -- rather than a de Bruijn index.
        let pdeps = usedNamesIn pvars i (delab i cwvalty)
        let (bargs_pre, bargs_post) = split pdeps bargs []
        logLvl 10 ("With type " ++ show (getRetTy cwvaltyN) ++
                  " depends on " ++ show pdeps ++ " from " ++ show pvars)
        logLvl 10 ("Pre " ++ show bargs_pre ++ "\nPost " ++ show bargs_post)
        windex <- getName
        -- build a type declaration for the new function:
        -- (ps : Xs) -> (withval : cwvalty) -> (ps' : Xs') -> ret_ty
        let wargval = getRetTy cwvalN
        let wargtype = getRetTy cwvaltyN
        logLvl 5 ("Abstract over " ++ show wargval)
        let wtype = bindTyArgs Pi (bargs_pre ++
                     (sMN 0 "warg", wargtype) :
                     map (abstract (sMN 0 "warg") wargval wargtype) bargs_post)
                     (substTerm wargval (P Bound (sMN 0 "warg") wargtype) ret_ty)
        logLvl 3 ("New function type " ++ show wtype)
        let wname = sMN windex (show fname)

        let imps = getImps wtype -- add to implicits context
        putIState (i { idris_implicits = addDef wname imps (idris_implicits i) })
        addIBC (IBCDef wname)
        def' <- checkDef fc [(wname, (-1, Nothing, wtype))]
        let def'' = map (\(n, (i, top, t)) -> (n, (i, top, t, False))) def'
        addDeferred def''

        -- in the subdecls, lhs becomes:
        --         fname  pats | wpat [rest]
        --    ==>  fname' ps   wpat [rest], match pats against toplevel for ps
        wb <- mapM (mkAuxC wname lhs (map fst bargs_pre) (map fst bargs_post))
                       withblock
        logLvl 3 ("with block " ++ show wb)
        -- propagate totality assertion to the new definitions
        when (AssertTotal `elem` opts) $ setFlags wname [AssertTotal]
        mapM_ (elabDecl EAll info) wb

        -- rhs becomes: fname' ps wval
        let rhs = PApp fc (PRef fc wname)
                    (map (pexp . (PRef fc) . fst) bargs_pre ++
                        pexp wval :
                    (map (pexp . (PRef fc) . fst) bargs_post))
        logLvl 5 ("New RHS " ++ showTmImpls rhs)
        ctxt <- getContext -- New context with block added
        i <- getIState
        ((rhs', defer, is), _) <-
           tclift $ elaborate ctxt (sMN 0 "wpatRHS") clhsty []
                    (do pbinds i lhs_tm
                        setNextName
                        (_, d, is) <- erun fc (build i info False opts fname rhs)
                        psolve lhs_tm
                        tt <- get_term
                        return (tt, d, is))
        def' <- checkDef fc defer
        let def'' = map (\(n, (i, top, t)) -> (n, (i, top, t, False))) def'
        addDeferred def''
        mapM_ (elabCaseBlock info opts) is
        logLvl 5 ("Checked RHS " ++ show rhs')
        (crhs, crhsty) <- recheckC fc [] rhs'
        return $ (Right (clhs, crhs), lhs)
  where
    getImps (Bind n (Pi _) t) = pexp Placeholder : getImps t
    getImps _ = []

    mkAuxC wname lhs ns ns' (PClauses fc o n cs)
        | True  = do cs' <- mapM (mkAux wname lhs ns ns') cs
                     return $ PClauses fc o wname cs'
        | otherwise = ifail $ show fc ++ "with clause uses wrong function name " ++ show n
    mkAuxC wname lhs ns ns' d = return $ d

    mkAux wname toplhs ns ns' (PClause fc n tm_in (w:ws) rhs wheres)
        = do i <- getIState
             let tm = addImplPat i tm_in
             logLvl 2 ("Matching " ++ showTmImpls tm ++ " against " ++
                                      showTmImpls toplhs)
             case matchClause i toplhs tm of
                Left (a,b) -> trace ("matchClause: " ++ show a ++ " =/= " ++ show b) (ifail $ show fc ++ ":with clause does not match top level")
                Right mvars ->
                    do logLvl 3 ("Match vars : " ++ show mvars)
                       lhs <- updateLHS n wname mvars ns ns' (fullApp tm) w
                       return $ PClause fc wname lhs ws rhs wheres
    mkAux wname toplhs ns ns' (PWith fc n tm_in (w:ws) wval withs)
        = do i <- getIState
             let tm = addImplPat i tm_in
             logLvl 2 ("Matching " ++ showTmImpls tm ++ " against " ++
                                      showTmImpls toplhs)
             withs' <- mapM (mkAuxC wname toplhs ns ns') withs
             case matchClause i toplhs tm of
                Left (a,b) -> trace ("matchClause: " ++ show a ++ " =/= " ++ show b) (ifail $ show fc ++ "with clause does not match top level")
                Right mvars ->
                    do lhs <- updateLHS n wname mvars ns ns' (fullApp tm) w
                       return $ PWith fc wname lhs ws wval withs'
    mkAux wname toplhs ns ns' c
        = ifail $ show fc ++ ":badly formed with clause"

    addArg (PApp fc f args) w = PApp fc f (args ++ [pexp w])
    addArg (PRef fc f) w = PApp fc (PRef fc f) [pexp w]

    updateLHS n wname mvars ns_in ns_in' (PApp fc (PRef fc' n') args) w
        = let ns = map (keepMvar (map fst mvars) fc') ns_in
              ns' = map (keepMvar (map fst mvars) fc') ns_in' in
              return $ substMatches mvars $
                  PApp fc (PRef fc' wname)
                      (map pexp ns ++ pexp w : (map pexp ns'))
    updateLHS n wname mvars ns_in ns_in' tm w
        = updateLHS n wname mvars ns_in ns_in' (PApp fc tm []) w

    keepMvar mvs fc v | v `elem` mvs = PRef fc v
                      | otherwise = Placeholder

    fullApp (PApp _ (PApp fc f args) xs) = fullApp (PApp fc f (args ++ xs))
    fullApp x = x

    split [] rest pre = (reverse pre, rest)
    split deps ((n, ty) : rest) pre
          | n `elem` deps = split (deps \\ [n]) rest ((n, ty) : pre)
          | otherwise = split deps rest ((n, ty) : pre)
    split deps [] pre = (reverse pre, [])

    abstract wn wv wty (n, argty) = (n, substTerm wv (P Bound wn wty) argty)

data MArgTy = IA | EA | CA deriving Show

elabClass :: ElabInfo -> SyntaxInfo -> Docstring ->
             FC -> [PTerm] ->
             Name -> [(Name, PTerm)] -> [(Name, Docstring)] -> [PDecl] -> Idris ()
elabClass info syn doc fc constraints tn ps pDocs ds
    = do let cn = SN (InstanceCtorN tn) -- sUN ("instance" ++ show tn) -- MN 0 ("instance" ++ show tn)
         let tty = pibind ps PType
         let constraint = PApp fc (PRef fc tn)
                                  (map (pexp . PRef fc) (map fst ps))
         -- build data declaration
         let mdecls = filter tydecl ds -- method declarations
         let idecls = filter instdecl ds -- default superclass instance declarations
         mapM_ checkDefaultSuperclassInstance idecls
         let mnames = map getMName mdecls
         logLvl 2 $ "Building methods " ++ show mnames
         ims <- mapM (tdecl mnames) mdecls
         defs <- mapM (defdecl (map (\ (x,y,z) -> z) ims) constraint)
                      (filter clause ds)
         let (methods, imethods)
              = unzip (map (\ ( x,y,z) -> (x, y)) ims)
         let defaults = map (\ (x, (y, z)) -> (x,y)) defs
         addClass tn (CI cn (map nodoc imethods) defaults idecls (map fst ps) [])
         -- build instance constructor type
         -- decorate names of functions to ensure they can't be referred
         -- to elsewhere in the class declaration
         let cty = impbind ps $ conbind constraints
                      $ pibind (map (\ (n, ty) -> (nsroot n, ty)) methods)
                               constraint
         let cons = [(emptyDocstring, [], cn, cty, fc, [])]
         let ddecl = PDatadecl tn tty cons
         logLvl 5 $ "Class data " ++ show (showDImp verbosePPOption ddecl)
         elabData info (syn { no_imp = no_imp syn ++ mnames }) doc pDocs fc [] ddecl
         -- for each constraint, build a top level function to chase it
         logLvl 5 $ "Building functions"
         let usyn = syn { using = map (\ (x,y) -> UImplicit x y) ps
                                      ++ using syn }
         fns <- mapM (cfun cn constraint usyn (map fst imethods)) constraints
         mapM_ (elabDecl EAll info) (concat fns)
         -- for each method, build a top level function
         fns <- mapM (tfun cn constraint usyn (map fst imethods)) imethods
         mapM_ (elabDecl EAll info) (concat fns)
         -- add the default definitions
         mapM_ (elabDecl EAll info) (concat (map (snd.snd) defs))
         addIBC (IBCClass tn)
  where
    nodoc (n, (_, o, t)) = (n, (o, t))
    pibind [] x = x
    pibind ((n, ty): ns) x = PPi expl n ty (pibind ns x)

    mdec (UN n) = SN (MethodN (UN n))
    mdec (NS x n) = NS (mdec x) n
    mdec x = x

    -- TODO: probably should normalise
    checkDefaultSuperclassInstance (PInstance _ fc cs n ps _ _ _)
        = do when (not $ null cs) . tclift
                $ tfail (At fc (Msg $ "Default superclass instances can't have constraints."))
             i <- getIState
             let t = PApp fc (PRef fc n) (map pexp ps)
             let isConstrained = any (== t) constraints
             when (not isConstrained) . tclift
                $ tfail (At fc (Msg $ "Default instances must be for a superclass constraint on the containing class."))
             return ()

    impbind [] x = x
    impbind ((n, ty): ns) x = PPi impl n ty (impbind ns x)
    conbind (ty : ns) x = PPi constraint (sMN 0 "class") ty (conbind ns x)
    conbind [] x = x

    getMName (PTy _ _ _ _ _ n _) = nsroot n
    tdecl allmeths (PTy doc _ syn _ o n t)
           = do t' <- implicit' info syn allmeths n t
                logLvl 5 $ "Method " ++ show n ++ " : " ++ showTmImpls t'
                return ( (n, (toExp (map fst ps) Exp t')),
                         (n, (doc, o, (toExp (map fst ps) Imp t'))),
                         (n, (syn, o, t) ) )
    tdecl _ _ = ifail "Not allowed in a class declaration"

    -- Create default definitions
    defdecl mtys c d@(PClauses fc opts n cs) =
        case lookup n mtys of
            Just (syn, o, ty) -> do let ty' = insertConstraint c ty
                                    let ds = map (decorateid defaultdec)
                                                 [PTy emptyDocstring [] syn fc [] n ty',
                                                  PClauses fc (o ++ opts) n cs]
                                    iLOG (show ds)
                                    return (n, ((defaultdec n, ds!!1), ds))
            _ -> ifail $ show n ++ " is not a method"
    defdecl _ _ _ = ifail "Can't happen (defdecl)"

    defaultdec (UN n) = sUN ("default#" ++ str n)
    defaultdec (NS n ns) = NS (defaultdec n) ns

    tydecl (PTy _ _ _ _ _ _ _) = True
    tydecl _ = False
    instdecl (PInstance _ _ _ _ _ _ _ _) = True
    instdecl _ = False
    clause (PClauses _ _ _ _) = True
    clause _ = False

    -- Generate a function for chasing a dictionary constraint
    cfun cn c syn all con
        = do let cfn = sUN ('@':'@':show cn ++ "#" ++ show con)
                       -- SN (ParentN cn (show con))
             let mnames = take (length all) $ map (\x -> sMN x "meth") [0..]
             let capp = PApp fc (PRef fc cn) (map (pexp . PRef fc) mnames)
             let lhs = PApp fc (PRef fc cfn) [pconst capp]
             let rhs = PResolveTC (fileFC "HACK")
             let ty = PPi constraint (sMN 0 "pc") c con
             iLOG (showTmImpls ty)
             iLOG (showTmImpls lhs ++ " = " ++ showTmImpls rhs)
             i <- getIState
             let conn = case con of
                            PRef _ n -> n
                            PApp _ (PRef _ n) _ -> n
             let conn' = case lookupCtxtName conn (idris_classes i) of
                                [(n, _)] -> n
                                _ -> conn
             addInstance False conn' cfn
             addIBC (IBCInstance False conn' cfn)
--              iputStrLn ("Added " ++ show (conn, cfn, ty))
             return [PTy emptyDocstring [] syn fc [] cfn ty,
                     PClauses fc [Dictionary] cfn [PClause fc cfn lhs [] rhs []]]

    -- Generate a top level function which looks up a method in a given
    -- dictionary (this is inlinable, always)
    tfun cn c syn all (m, (doc, o, ty))
        = do let ty' = insertConstraint c ty
             let mnames = take (length all) $ map (\x -> sMN x "meth") [0..]
             let capp = PApp fc (PRef fc cn) (map (pexp . PRef fc) mnames)
             let margs = getMArgs ty
             let anames = map (\x -> sMN x "arg") [0..]
             let lhs = PApp fc (PRef fc m) (pconst capp : lhsArgs margs anames)
             let rhs = PApp fc (getMeth mnames all m) (rhsArgs margs anames)
             iLOG (showTmImpls ty)
             iLOG (show (m, ty', capp, margs))
             iLOG (showTmImpls lhs ++ " = " ++ showTmImpls rhs)
             return [PTy doc [] syn fc o m ty',
                     PClauses fc [Inlinable] m [PClause fc m lhs [] rhs []]]

    getMArgs (PPi (Imp _ _ _) n ty sc) = IA : getMArgs sc
    getMArgs (PPi (Exp _ _ _) n ty sc) = EA  : getMArgs sc
    getMArgs (PPi (Constraint _ _) n ty sc) = CA : getMArgs sc
    getMArgs _ = []

    getMeth (m:ms) (a:as) x | x == a = PRef fc m
                            | otherwise = getMeth ms as x

    lhsArgs (EA : xs) (n : ns) = [] -- pexp (PRef fc n) : lhsArgs xs ns
    lhsArgs (IA : xs) ns = lhsArgs xs ns
    lhsArgs (CA : xs) ns = lhsArgs xs ns
    lhsArgs [] _ = []

    rhsArgs (EA : xs) (n : ns) = [] -- pexp (PRef fc n) : rhsArgs xs ns
    rhsArgs (IA : xs) ns = pexp Placeholder : rhsArgs xs ns
    rhsArgs (CA : xs) ns = pconst (PResolveTC fc) : rhsArgs xs ns
    rhsArgs [] _ = []

    insertConstraint c (PPi p@(Imp _ _ _) n ty sc)
                          = PPi p n ty (insertConstraint c sc)
    insertConstraint c sc = PPi constraint (sMN 0 "class") c sc

    -- make arguments explicit and don't bind class parameters
    toExp ns e (PPi (Imp l s p) n ty sc)
        | n `elem` ns = toExp ns e sc
        | otherwise = PPi (e l s p) n ty (toExp ns e sc)
    toExp ns e (PPi p n ty sc) = PPi p n ty (toExp ns e sc)
    toExp ns e sc = sc

elabInstance :: ElabInfo -> SyntaxInfo ->
                ElabWhat -> -- phase
                FC -> [PTerm] -> -- constraints
                Name -> -- the class
                [PTerm] -> -- class parameters (i.e. instance)
                PTerm -> -- full instance type
                Maybe Name -> -- explicit name
                [PDecl] -> Idris ()
elabInstance info syn what fc cs n ps t expn ds = do
    i <- getIState
    (n, ci) <- case lookupCtxtName n (idris_classes i) of
                  [c] -> return c
                  [] -> ifail $ show fc ++ ":" ++ show n ++ " is not a type class"
                  cs -> tclift $ tfail $ At fc 
                           (CantResolveAlts (map fst cs))
    let constraint = PApp fc (PRef fc n) (map pexp ps)
    let iname = mkiname n ps expn
    let emptyclass = null (class_methods ci)
    when (what /= EDefns || (null ds && not emptyclass)) $ do
         nty <- elabType' True info syn emptyDocstring [] fc [] iname t
         -- if the instance type matches any of the instances we have already,
         -- and it's not a named instance, then it's overlapping, so report an error
         case expn of
            Nothing -> do mapM_ (maybe (return ()) overlapping . findOverlapping i (delab i nty))
                                (class_instances ci)
                          addInstance intInst n iname
            Just _ -> addInstance intInst n iname
    when (what /= ETypes && (not (null ds && not emptyclass))) $ do 
         let ips = zip (class_params ci) ps
         let ns = case n of
                    NS n ns' -> ns'
                    _ -> []
         -- get the implicit parameters that need passing through to the
         -- where block
         wparams <- mapM (\p -> case p of
                                  PApp _ _ args -> getWParams (map getTm args)
                                  _ -> return []) ps
         let pnames = map pname (concat (nub wparams))
         let superclassInstances = map (substInstance ips pnames) (class_default_superclasses ci)
         undefinedSuperclassInstances <- filterM (fmap not . isOverlapping i) superclassInstances
         mapM_ (elabDecl EAll info) undefinedSuperclassInstances
         let all_meths = map (nsroot . fst) (class_methods ci)
         let mtys = map (\ (n, (op, t)) ->
                   let t_in = substMatchesShadow ips pnames t 
                       mnamemap = map (\n -> (n, PRef fc (decorate ns iname n)))
                                      all_meths
                       t' = substMatchesShadow mnamemap pnames t_in in
                       (decorate ns iname n,
                           op, coninsert cs t', t'))
              (class_methods ci)
         logLvl 3 (show (mtys, ips))
         let ds' = insertDefaults i iname (class_defaults ci) ns ds
         iLOG ("Defaults inserted: " ++ show ds' ++ "\n" ++ show ci)
         mapM_ (warnMissing ds' ns iname) (map fst (class_methods ci))
         mapM_ (checkInClass (map fst (class_methods ci))) (concatMap defined ds')
         let wbTys = map mkTyDecl mtys
         let wbVals = map (decorateid (decorate ns iname)) ds'
         let wb = wbTys ++ wbVals
         logLvl 3 $ "Method types " ++ showSep "\n" (map (show . showDeclImp verbosePPOption . mkTyDecl) mtys)
         logLvl 3 $ "Instance is " ++ show ps ++ " implicits " ++
                                      show (concat (nub wparams))

         -- Bring variables in instance head into scope
         ist <- getIState
         let headVars = nub $ mapMaybe (\p -> case p of
                                               PRef _ n -> 
                                                  case lookupTy n (tt_ctxt ist) of
                                                      [] -> Just n
                                                      _ -> Nothing
                                               _ -> Nothing) ps
--          let lhs = PRef fc iname
         let lhs = PApp fc (PRef fc iname)
                           (map (\n -> pimp n (PRef fc n) True) headVars)
         let rhs = PApp fc (PRef fc (instanceName ci))
                           (map (pexp . mkMethApp) mtys)

         logLvl 5 $ "Instance LHS " ++ show lhs ++ " " ++ show headVars
         logLvl 5 $ "Instance RHS " ++ show rhs

         let idecls = [PClauses fc [Dictionary] iname
                                 [PClause fc iname lhs [] rhs wb]]
         iLOG (show idecls)
         mapM_ (elabDecl EAll info) idecls
         addIBC (IBCInstance intInst n iname)

  where
    intInst = case ps of
                [PConstant (AType (ATInt ITNative))] -> True
                _ -> False

    mkiname n' ps' expn' =
        case expn' of
          Nothing -> SN (sInstanceN n' (map show ps'))
          Just nm -> nm

    substInstance ips pnames (PInstance syn _ cs n ps t expn ds)
        = PInstance syn fc cs n (map (substMatchesShadow ips pnames) ps) (substMatchesShadow ips pnames t) expn ds

    isOverlapping i (PInstance syn _ _ n ps t expn _)
        = case lookupCtxtName n (idris_classes i) of
            [(n, ci)] -> let iname = (mkiname n ps expn) in
                            case lookupTy iname (tt_ctxt i) of
                              [] -> elabFindOverlapping i ci iname syn t
                              (_:_) -> return True
            _ -> return False -- couldn't find class, just let elabInstance fail later

    -- TODO: largely based upon elabType' - should try to abstract
    elabFindOverlapping i ci iname syn t
        = do ty' <- addUsingConstraints syn fc t
             -- TODO think: something more in info?
             ty' <- implicit info syn iname ty'
             let ty = addImpl i ty'
             ctxt <- getContext
             ((tyT, _, _), _) <-
                   tclift $ elaborate ctxt iname (TType (UVal 0)) []
                            (errAt "type of " iname (erun fc (build i info False [] iname ty)))
             ctxt <- getContext
             (cty, _) <- recheckC fc [] tyT
             let nty = normalise ctxt [] cty
             return $ any (isJust . findOverlapping i (delab i nty)) (class_instances ci)

    findOverlapping i t n
     | take 2 (show n) == "@@" = Nothing
     | otherwise
        = case lookupTy n (tt_ctxt i) of
            [t'] -> let tret = getRetType t
                        tret' = getRetType (delab i t') in
                        case matchClause i tret' tret of
                            Right ms -> Just tret'
                            Left _ -> case matchClause i tret tret' of
                                Right ms -> Just tret'
                                Left _ -> Nothing
            _ -> Nothing
    overlapping t' = tclift $ tfail (At fc (Msg $
                          "Overlapping instance: " ++ show t' ++ " already defined"))
    getRetType (PPi _ _ _ sc) = getRetType sc
    getRetType t = t

    mkMethApp (n, _, _, ty)
          = lamBind 0 ty (papp fc (PRef fc n) (methArgs 0 ty))
    lamBind i (PPi (Constraint _ _) _ _ sc) sc'
          = PLam (sMN i "meth") Placeholder (lamBind (i+1) sc sc')
    lamBind i (PPi _ n ty sc) sc'
          = PLam (sMN i "meth") Placeholder (lamBind (i+1) sc sc')
    lamBind i _ sc = sc
    methArgs i (PPi (Imp _ _ _) n ty sc)
        = PImp 0 True [] n (PRef fc (sMN i "meth")) : methArgs (i+1) sc
    methArgs i (PPi (Exp _ _ _) n ty sc)
        = PExp 0 [] (sMN 0 "marg") (PRef fc (sMN i "meth")) : methArgs (i+1) sc
    methArgs i (PPi (Constraint _ _) n ty sc)
        = PConstraint 0 [] (sMN 0 "marg") (PResolveTC fc) : methArgs (i+1) sc
    methArgs i _ = []

    papp fc f [] = f
    papp fc f as = PApp fc f as

    getWParams [] = return []
    getWParams (p : ps)
      | PRef _ n <- p
        = do ps' <- getWParams ps
             ctxt <- getContext
             case lookupP n ctxt of
                [] -> return (pimp n (PRef fc n) True : ps')
                _ -> return ps'
    getWParams (_ : ps) = getWParams ps

    decorate ns iname (UN n)        = NS (SN (MethodN (UN n))) ns
    decorate ns iname (NS (UN n) s) = NS (SN (MethodN (UN n))) ns

    mkTyDecl (n, op, t, _) = PTy emptyDocstring [] syn fc op n t

    conbind (ty : ns) x = PPi constraint (sMN 0 "class") ty (conbind ns x)
    conbind [] x = x

    coninsert cs (PPi p@(Imp _ _ _) n t sc) = PPi p n t (coninsert cs sc)
    coninsert cs sc = conbind cs sc

    insertDefaults :: IState -> Name ->
                      [(Name, (Name, PDecl))] -> [T.Text] ->
                      [PDecl] -> [PDecl]
    insertDefaults i iname [] ns ds = ds
    insertDefaults i iname ((n,(dn, clauses)) : defs) ns ds
       = insertDefaults i iname defs ns (insertDef i n dn clauses ns iname ds)

    insertDef i meth def clauses ns iname decls
        | null $ filter (clauseFor meth iname ns) decls
            = let newd = expandParamsD False i (\n -> meth) [] [def] clauses in
                  -- trace (show newd) $
                  decls ++ [newd]
        | otherwise = decls

    warnMissing decls ns iname meth
        | null $ filter (clauseFor meth iname ns) decls
            = iWarn fc . text $ "method " ++ show meth ++ " not defined"
        | otherwise = return ()

    checkInClass ns meth
        | not (null (filter (eqRoot meth) ns)) = return ()
        | otherwise = tclift $ tfail (At fc (Msg $
                                show meth ++ " not a method of class " ++ show n))

    eqRoot x y = nsroot x == nsroot y

    clauseFor m iname ns (PClauses _ _ m' _)
       = decorate ns iname m == decorate ns iname m'
    clauseFor m iname ns _ = False

{- This won't work yet. Can it ever, in this form?

    cfun cn c syn all con
        = do let cfn = UN ('@':'@':show cn ++ "#" ++ show con)
             let mnames = take (length all) $ map (\x -> MN x "meth") [0..]
             let capp = PApp fc (PRef fc cn) (map (pexp . PRef fc) mnames)
             let lhs = PApp fc (PRef fc cfn) [pconst capp]
             let rhs = PResolveTC (FC "HACK" 0)
             let ty = PPi constraint (MN 0 "pc") c con
             iLOG (showImp True ty)
             iLOG (showImp True lhs ++ " = " ++ showImp True rhs)
             i <- getIState
             let conn = case con of
                            PRef _ n -> n
                            PApp _ (PRef _ n) _ -> n
             let conn' = case lookupCtxtName Nothing conn (idris_classes i) of
                                [(n, _)] -> n
                                _ -> conn
             addInstance False conn' cfn
             addIBC (IBCInstance False conn' cfn)
             iputStrLn ("Added " ++ show (conn, cfn, ty) ++ "\n" ++ show (lhs, rhs))
             return [PTy "" syn fc [] cfn ty,
                     PClauses fc [Dictionary] cfn [PClause fc cfn lhs [] rhs []]]
-}

decorateid decorate (PTy doc argdocs s f o n t) = PTy doc argdocs s f o (decorate n) t
decorateid decorate (PClauses f o n cs)
   = PClauses f o (decorate n) (map dc cs)
    where dc (PClause fc n t as w ds) = PClause fc (decorate n) (dappname t) as w ds
          dc (PWith   fc n t as w ds)
                 = PWith fc (decorate n) (dappname t) as w
                            (map (decorateid decorate) ds)
          dappname (PApp fc (PRef fc' n) as) = PApp fc (PRef fc' (decorate n)) as
          dappname t = t


-- if 't' is a type class application, assume its arguments are injective
pbinds :: IState -> Term -> ElabD ()
pbinds i (Bind n (PVar t) sc) 
    = do attack; patbind n
         case unApply t of
              (P _ c _, args) -> case lookupCtxt c (idris_classes i) of
                                   [] -> return ()
                                   _ -> -- type class, set as injective
                                        mapM_ setinjArg args
              _ -> return ()
         pbinds i sc
  where setinjArg (P _ n _) = setinj n
        setinjArg _ = return ()
pbinds i tm = return ()

pbty (Bind n (PVar t) sc) tm = Bind n (PVTy t) (pbty sc tm)
pbty _ tm = tm

getPBtys (Bind n (PVar t) sc) = (n, t) : getPBtys sc
getPBtys (Bind n (PVTy t) sc) = (n, t) : getPBtys sc
getPBtys _ = []

psolve (Bind n (PVar t) sc) = do solve; psolve sc
psolve tm = return ()

pvars ist (Bind n (PVar t) sc) = (n, delab ist t) : pvars ist sc
pvars ist _ = []

data ElabWhat = ETypes | EDefns | EAll
  deriving (Show, Eq)

elabDecls :: ElabInfo -> [PDecl] -> Idris ()
elabDecls info ds = do mapM_ (elabDecl EAll info) ds
--                       mapM_ (elabDecl EDefns info) ds

elabDecl :: ElabWhat -> ElabInfo -> PDecl -> Idris ()
elabDecl what info d
    = idrisCatch (withErrorReflection $ elabDecl' what info d) (setAndReport)

elabDecl' _ info (PFix _ _ _)
     = return () -- nothing to elaborate
elabDecl' _ info (PSyntax _ p)
     = return () -- nothing to elaborate
elabDecl' what info (PTy doc argdocs s f o n ty)
  | what /= EDefns
    = do iLOG $ "Elaborating type decl " ++ show n ++ show o
         elabType info s doc argdocs f o n ty
         return ()
elabDecl' what info (PPostulate doc s f o n ty)
  | what /= EDefns
    = do iLOG $ "Elaborating postulate " ++ show n ++ show o
         elabPostulate info s doc f o n ty
elabDecl' what info (PData doc argDocs s f co d)
  | what /= ETypes
    = do iLOG $ "Elaborating " ++ show (d_name d)
         elabData info s doc argDocs f co d
  | otherwise
    = do iLOG $ "Elaborating [type of] " ++ show (d_name d)
         elabData info s doc argDocs f co (PLaterdecl (d_name d) (d_tcon d))
elabDecl' what info d@(PClauses f o n ps)
  | what /= ETypes
    = do iLOG $ "Elaborating clause " ++ show n
         i <- getIState -- get the type options too
         let o' = case lookupCtxt n (idris_flags i) of
                    [fs] -> fs
                    [] -> []
         elabClauses info f (o ++ o') n ps
elabDecl' what info (PMutual f ps)
    = do case ps of
              [p] -> elabDecl what info p
              _ -> do mapM_ (elabDecl ETypes info) ps
                      mapM_ (elabDecl EDefns info) ps
         -- record mutually defined data definitions
         let datans = concatMap declared (filter isDataDecl ps)
         mapM_ (setMutData datans) datans
         iLOG $ "Rechecking for positivity " ++ show datans
         mapM_ (\x -> do setTotality x Unchecked) datans
         -- Do totality checking after entire mutual block
         i <- get
         mapM_ (\n -> do logLvl 5 $ "Simplifying " ++ show n
                         updateContext (simplifyCasedef n $ getErasureInfo i))
                 (map snd (idris_totcheck i))
         mapM_ buildSCG (idris_totcheck i)
         mapM_ checkDeclTotality (idris_totcheck i)
         clear_totcheck
  where isDataDecl (PData _ _ _ _ _ _) = True
        isDataDecl _ = False

        setMutData ns n 
           = do i <- getIState
                case lookupCtxt n (idris_datatypes i) of
                   [x] -> do let x' = x { mutual_types = ns }
                             putIState $ i { idris_datatypes 
                                                = addDef n x' (idris_datatypes i) }
                   _ -> return ()

elabDecl' what info (PParams f ns ps)
    = do i <- getIState
         iLOG $ "Expanding params block with " ++ show ns ++ " decls " ++
                show (concatMap tldeclared ps)
         let nblock = pblock i
         mapM_ (elabDecl' what info) nblock
  where
    pinfo = let ds = concatMap tldeclared ps
                newps = params info ++ ns
                dsParams = map (\n -> (n, map fst newps)) ds
                newb = addAlist dsParams (inblock info) in
                info { params = newps,
                       inblock = newb }
    pblock i = map (expandParamsD False i id ns
                      (concatMap tldeclared ps)) ps

elabDecl' what info (PNamespace n ps) = mapM_ (elabDecl' what ninfo) ps
  where
    ninfo = case namespace info of
                Nothing -> info { namespace = Just [n] }
                Just ns -> info { namespace = Just (n:ns) }
elabDecl' what info (PClass doc s f cs n ps pdocs ds)
  | what /= EDefns
    = do iLOG $ "Elaborating class " ++ show n
         elabClass info (s { syn_params = [] }) doc f cs n ps pdocs ds
elabDecl' what info (PInstance s f cs n ps t expn ds)
    = do iLOG $ "Elaborating instance " ++ show n
         elabInstance info s what f cs n ps t expn ds
elabDecl' what info (PRecord doc s f tyn ty opts cdoc cn cty)
  | what /= ETypes
    = do iLOG $ "Elaborating record " ++ show tyn
         elabRecord info s doc f tyn ty opts cdoc cn cty
  | otherwise
    = do iLOG $ "Elaborating [type of] " ++ show tyn
         elabData info s doc [] f [] (PLaterdecl tyn ty)
elabDecl' _ info (PDSL n dsl)
    = do i <- getIState
         putIState (i { idris_dsls = addDef n dsl (idris_dsls i) })
         addIBC (IBCDSL n)
elabDecl' what info (PDirective i)
  | what /= EDefns = i
elabDecl' what info (PProvider syn fc provWhat n)
  | what /= EDefns
    = do iLOG $ "Elaborating type provider " ++ show n
         elabProvider info syn fc provWhat n
elabDecl' what info (PTransform fc safety old new)
    = elabTransform info fc safety old new
elabDecl' _ _ _ = return () -- skipped this time

elabCaseBlock info opts d@(PClauses f o n ps)
        = do addIBC (IBCDef n)
             logLvl 5 $ "CASE BLOCK: " ++ show (n, d)
             let opts' = nub (o ++ opts)
             -- propagate totality assertion to the new definitions
             when (AssertTotal `elem` opts) $ setFlags n [AssertTotal]
             elabDecl' EAll info (PClauses f opts' n ps )

-- elabDecl' info (PImport i) = loadModule i

-- Check that the result of type checking matches what the programmer wrote
-- (i.e. - if we inferred any arguments that the user provided, make sure
-- they are the same!)

checkInferred :: FC -> PTerm -> PTerm -> Idris ()
checkInferred fc inf user =
     do logLvl 6 $ "Checked to\n" ++ showTmImpls inf ++ "\n\nFROM\n\n" ++
                                     showTmImpls user
        logLvl 10 $ "Checking match"
        i <- getIState
        tclift $ case matchClause' True i user inf of
            _ -> return ()
--             Left (x, y) -> tfail $ At fc
--                                     (Msg $ "The type-checked term and given term do not match: "
--                                            ++ show x ++ " and " ++ show y)
        logLvl 10 $ "Checked match"
--                           ++ "\n" ++ showImp True inf ++ "\n" ++ showImp True user)

-- Return whether inferred term is different from given term
-- (as above, but return a Bool)

inferredDiff :: FC -> PTerm -> PTerm -> Idris Bool
inferredDiff fc inf user =
     do i <- getIState
        logLvl 6 $ "Checked to\n" ++ showTmImpls inf ++ "\n" ++
                                     showTmImpls user
        tclift $ case matchClause' True i user inf of
            Right vs -> return False
            Left (x, y) -> return True

-- | Check a PTerm against documentation and ensure that every documented
-- argument actually exists.  This must be run _after_ implicits have been
-- found, or it will give spurious errors.
checkDocs :: FC -> [(Name, Docstring)] -> PTerm -> Idris ()
checkDocs fc args tm = cd (Map.fromList args) tm
  where cd as (PPi _ n _ sc) = cd (Map.delete n as) sc
        cd as _ | Map.null as = return ()
                | otherwise   = ierror . At fc . Msg $
                                "There is documentation for argument(s) "
                                ++ (concat . intersperse ", " . map show . Map.keys) as
                                ++ " but they were not found."

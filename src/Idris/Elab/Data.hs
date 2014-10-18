{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Data(elabData) where

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

import Idris.Elab.Type
import Idris.Elab.Utils
import Idris.Elab.Value

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

elabData :: ElabInfo -> SyntaxInfo -> Docstring (Either Err PTerm)-> [(Name, Docstring (Either Err PTerm))] -> FC -> DataOpts -> PData -> Idris ()
elabData info syn doc argDocs fc opts (PLaterdecl n t_in)
    = do let codata = Codata `elem` opts
         iLOG (show (fc, doc))
         checkUndefined fc n
         (cty, _, t, inacc) <- buildType info syn fc [] n t_in

         addIBC (IBCDef n)
         updateContext (addTyDecl n (TCon 0 0) cty) -- temporary, to check cons

elabData info syn doc argDocs fc opts (PDatadecl n t_in dcons)
    = do let codata = Codata `elem` opts
         iLOG (show fc)
         undef <- isUndefined fc n
         (cty, _, t, inacc) <- buildType info syn fc [] n t_in
         -- if n is defined already, make sure it is just a type declaration
         -- with the same type we've just elaborated
         i <- getIState
         checkDefinedAs fc n cty (tt_ctxt i)
         -- temporary, to check cons
         when undef $ updateContext (addTyDecl n (TCon 0 0) cty)
         let cnameinfo = cinfo info (map cname dcons)
         let unique = case getRetTy cty of
                           UType UniqueType -> True
                           _ -> False
         cons <- mapM (elabCon cnameinfo syn n codata (getRetTy cty)) dcons
         ttag <- getName
         i <- getIState
         let as = map (const (Left (Msg ""))) (getArgTys cty)
         let params = findParams  (map snd cons)
         logLvl 2 $ "Parameters : " ++ show params
         -- TI contains information about mutually declared types - this will
         -- be updated when the mutual block is complete
         putIState (i { idris_datatypes =
                          addDef n (TI (map fst cons) codata opts params [n])
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
        findParams ts = let allapps = map getDataApp ts
           -- do each constructor separately, then merge the results (names
           -- may change between constructors)
                            conParams = map paramPos allapps in
                            inAll conParams

        inAll :: [[Int]] -> [Int]
        inAll [] = []
        inAll (x : xs) = filter (\p -> all (\ps -> p `elem` ps) xs) x

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
        getDataApp (Bind n (Pi t _) sc)
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

elabCon :: ElabInfo -> SyntaxInfo -> Name -> Bool ->
           Type -> -- for kind checking
           (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, PTerm, FC, [Name]) ->
           Idris (Name, Type)
elabCon info syn tn codata expkind (doc, argDocs, n, t_in, fc, forcenames)
    = do checkUndefined fc n
         (cty, ckind, t, inacc) <- buildType info syn fc [Constructor] n (if codata then mkLazy t_in else t_in)
         ctxt <- getContext
         let cty' = normalise ctxt [] cty
         checkUniqueKind ckind expkind

         -- Check that the constructor type is, in fact, a part of the family being defined
         tyIs n cty'

         logLvl 2 $ show fc ++ ":Constructor " ++ show n ++ " : " ++ show t
         logLvl 5 $ "Inaccessible args: " ++ show inacc
         logLvl 2 $ "---> " ++ show n ++ " : " ++ show cty'

         addIBC (IBCDef n)
         checkDocs fc argDocs t
         doc' <- elabDocTerms info doc
         argDocs' <- mapM (\(n, d) -> do d' <- elabDocTerms info d
                                         return (n, d')) argDocs
         addDocStr n doc' argDocs'
         addIBC (IBCDoc n)
         fputState (opt_inaccessible . ist_optimisation n) inacc
         addIBC (IBCOpt n)
         return (n, cty')
  where
    tyIs con (Bind n b sc) = tyIs con sc
    tyIs con t | (P _ n' _, _) <- unApply t
        = if n' /= tn then tclift $ tfail (At fc (Elaborating "constructor " con (Msg (show n' ++ " is not " ++ show tn))))
             else return ()
    tyIs con t = tclift $ tfail (At fc (Elaborating "constructor " con (Msg (show t ++ " is not " ++ show tn))))

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

    -- if the constructor is a UniqueType, the datatype must be too
    -- (Type* is fine, since that is checked for uniqueness too)
    checkUniqueKind (UType NullType) (UType NullType) = return ()
    checkUniqueKind (UType NullType) _
        = tclift $ tfail (At fc (UniqueKindError NullType n))
    checkUniqueKind (UType UniqueType) (UType UniqueType) = return ()
    checkUniqueKind (UType UniqueType) (UType AllTypes) = return ()
    checkUniqueKind (UType UniqueType) (TType _)
        = tclift $ tfail (At fc (UniqueKindError UniqueType n))
    checkUniqueKind (UType AllTypes) _ = return ()
    checkUniqueKind (TType _) _ = return ()

type EliminatorState = StateT (Map.Map String Int) Idris

-- -- Issue #1616 in the issue tracker.
--     https://github.com/idris-lang/Idris-dev/issues/1616
--
-- TODO: Rewrite everything to use idris_implicits instead of manual splitting (or in TT)
-- FIXME: Many things have name starting with elim internally since this was the only purpose in the first edition of the function
-- rename to caseFun to match updated intend
elabCaseFun :: Bool -> [Int] -> Name -> PTerm ->
                  [(Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, PTerm, FC, [Name])] ->
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
  let eliminatorTyDecl = PTy (fmap (const (Left $ Msg "")) . parseDocstring . T.pack $ show n) [] defaultSyntax elimFC [TotalFn] elimDeclName eliminatorTy
  let clauseConsElimArgs = map getPiName consTerms
  let clauseGeneralArgs' = map getPiName generalParams ++ [motiveName] ++ clauseConsElimArgs
  let clauseGeneralArgs  = map (\arg -> pexp (PRef elimFC arg)) clauseGeneralArgs'
  let elimSig = "-- case function signature: " ++ showTmImpls eliminatorTy
  elimLog elimSig
  eliminatorClauses <- mapM (\(cns, cnsElim) -> generateEliminatorClauses cns cnsElim clauseGeneralArgs generalParams) (zip cons clauseConsElimArgs)
  let eliminatorDef = PClauses emptyFC [TotalFn] elimDeclName eliminatorClauses
  elimLog $ "-- case function definition: " ++ (show . showDeclImp verbosePPOption) eliminatorDef
  State.lift $ idrisCatch (rec_elabDecl info EAll info eliminatorTyDecl) (\err -> return ())
  -- Do not elaborate clauses if there aren't any
  case eliminatorClauses of
    [] -> State.lift $ solveDeferred elimDeclName -- Remove meta-variable for type
    _  -> State.lift $ idrisCatch (rec_elabDecl info EAll info eliminatorDef) (\err -> return ())
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

        extractConsTerm :: (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, PTerm, FC, [Name]) -> [(Name, Plicity, PTerm)] -> EliminatorState PTerm
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

        generateEliminatorClauses :: (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, PTerm, FC, [Name]) -> Name -> [PArg] -> [(Name, Plicity, PTerm)] -> EliminatorState PClause
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

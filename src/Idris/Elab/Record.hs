{-|
Module      : Idris.Elab.Record
Description : Code to elaborate records.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Record(elabRecord) where

import Idris.AbsSyntax
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Coverage
import Idris.DataOpts
import Idris.DeepSeq
import Idris.Delaborate
import Idris.Docstrings
import Idris.Elab.Data
import Idris.Elab.Data
import Idris.Elab.Term
import Idris.Elab.Type
import Idris.Elab.Utils
import Idris.Error
import Idris.Imports
import Idris.Inliner
import Idris.Output (iWarn, iputStrLn, pshow, sendHighlighting)
import Idris.Parser.Expr (tryFullExpr)
import Idris.PartialEval
import Idris.Primitives
import Idris.Providers
import IRTS.Lang

import Control.Monad
import Data.List
import Data.Maybe

-- | Elaborate a record declaration
elabRecord :: ElabInfo
           -> ElabWhat
           -> (Docstring (Either Err PTerm))                                             -- ^ The documentation for the whole declaration
           -> SyntaxInfo
           -> FC
           -> DataOpts
           -> Name                                                                       -- ^ The name of the type being defined
           -> FC                                                                         -- ^ The precise source location of the tycon name
           -> [(Name, FC, Plicity, PTerm)]                                               -- ^ Parameters
           -> [(Name, Docstring (Either Err PTerm))]                                     -- ^ Parameter Docs
           -> [(Maybe (Name, FC), Plicity, PTerm, Maybe (Docstring (Either Err PTerm)))] -- ^ Fields
           -> Maybe (Name, FC)                                                           -- ^ Constructor Name
           -> (Docstring (Either Err PTerm))                                             -- ^ Constructor Doc
           -> SyntaxInfo                                                                 -- ^ Constructor SyntaxInfo
           -> Idris ()
elabRecord info what doc rsyn fc opts tyn nfc params paramDocs fields cname cdoc csyn
  = do logElab 1 $ "Building data declaration for " ++ show tyn
       -- Type constructor
       let tycon = generateTyConType params
       logElab 1 $ "Type constructor " ++ showTmImpls tycon

       -- Data constructor
       dconName <- generateDConName (fmap fst cname)
       let dconTy = generateDConType params fieldsWithNameAndDoc
       logElab 1 $ "Data constructor: " ++ showTmImpls dconTy

       -- Build data declaration for elaboration
       logElab 1 $ foldr (++) "" $ intersperse "\n" (map show dconsArgDocs)
       let datadecl = case what of
                           ETypes -> PLaterdecl tyn NoFC tycon
                           _ -> PDatadecl tyn NoFC tycon [(cdoc, dconsArgDocs, dconName, NoFC, dconTy, fc, [])]
       elabData info rsyn doc paramDocs fc opts datadecl

       -- Keep track of the record
       let parameters = [(n,pt) | (n, _, _, pt) <- params]
       let projections = [n | (n, _, _, _, _) <- fieldsWithName]
       addRecord tyn (RI parameters dconName projections)
       addIBC (IBCRecord tyn)

       when (what /= ETypes) $ do
           logElab 1 $ "fieldsWithName " ++ show fieldsWithName
           logElab 1 $ "fieldsWIthNameAndDoc " ++ show fieldsWithNameAndDoc
           elabRecordFunctions info rsyn fc tyn paramsAndDoc fieldsWithNameAndDoc dconName target

           sendHighlighting $
             [(nfc, AnnName tyn Nothing Nothing Nothing)] ++
             maybe [] (\(_, cnfc) -> [(cnfc, AnnName dconName Nothing Nothing Nothing)]) cname ++
             [(ffc, AnnBoundName fn False) | (fn, ffc, _, _, _) <- fieldsWithName]

  where
    -- | Generates a type constructor.
    generateTyConType :: [(Name, FC, Plicity, PTerm)] -> PTerm
    generateTyConType ((n, nfc, p, t) : rest) = PPi p (nsroot n) nfc t (generateTyConType rest)
    generateTyConType [] = (PType fc)

    -- | Generates a name for the data constructor if none was specified.
    generateDConName :: Maybe Name -> Idris Name
    generateDConName (Just n) = return $ expandNS csyn n
    generateDConName Nothing  = uniqueName (expandNS csyn $ sMN 0 ("Mk" ++ (show (nsroot tyn))))
      where
        uniqueName :: Name -> Idris Name
        uniqueName n = do i <- getIState
                          case lookupTyNameExact n (tt_ctxt i) of
                            Just _  -> uniqueName (nextName n)
                            Nothing -> return n

    -- | Generates the data constructor type.
    generateDConType :: [(Name, FC, Plicity, PTerm)] -> [(Name, FC, Plicity, PTerm, a)] -> PTerm
    generateDConType ((n, nfc, _, t) : ps) as                  = PPi impl (nsroot n) NoFC t (generateDConType ps as)
    generateDConType []               ((n, _, p, t, _) : as) = PPi p    (nsroot n) NoFC t (generateDConType [] as)
    generateDConType [] [] = target

    -- | The target for the constructor and projection functions. Also the source of the update functions.
    target :: PTerm
    target = PApp fc (PRef fc [] tyn) $ map (uncurry asPRefArg) [(p, n) | (n, _, p, _) <- params]

    paramsAndDoc :: [(Name, FC, Plicity, PTerm, Docstring (Either Err PTerm))]
    paramsAndDoc = pad params paramDocs
      where
        pad :: [(Name, FC, Plicity, PTerm)] -> [(Name, Docstring (Either Err PTerm))] -> [(Name, FC, Plicity, PTerm, Docstring (Either Err PTerm))]
        pad ((n, fc, p, t) : rest) docs
          = let d = case lookup n docs of
                     Just d' -> d
                     Nothing -> emptyDocstring
            in (n, fc, p, t, d) : (pad rest docs)
        pad _ _ = []

    dconsArgDocs :: [(Name, Docstring (Either Err PTerm))]
    dconsArgDocs = paramDocs ++ (dcad fieldsWithName)
      where
        dcad :: [(Name, FC, Plicity, PTerm, Maybe (Docstring (Either Err PTerm)))] -> [(Name, Docstring (Either Err PTerm))]
        dcad ((n, _, _, _, (Just d)) : rest) = ((nsroot n), d) : (dcad rest)
        dcad (_ : rest) = dcad rest
        dcad [] = []

    fieldsWithName :: [(Name, FC, Plicity, PTerm, Maybe (Docstring (Either Err PTerm)))]
    fieldsWithName = fwn [] fields
      where
        fwn :: [Name] -> [(Maybe (Name, FC), Plicity, PTerm, Maybe (Docstring (Either Err PTerm)))] -> [(Name, FC, Plicity, PTerm, Maybe (Docstring (Either Err PTerm)))]
        fwn ns ((n, p, t, d) : rest)
          = let nn = case n of
                      Just n' -> n'
                      Nothing -> newName ns baseName
                withNS = expandNS rsyn (fst nn)
            in (withNS, snd nn, p, t, d) : (fwn (fst nn : ns) rest)
        fwn _ _ = []

        baseName = (sUN "__pi_arg", NoFC)

        newName :: [Name] -> (Name, FC) -> (Name, FC)
        newName ns (n, nfc)
          | n `elem` ns = newName ns (nextName n, nfc)
          | otherwise = (n, nfc)

    fieldsWithNameAndDoc :: [(Name, FC, Plicity, PTerm, Docstring (Either Err PTerm))]
    fieldsWithNameAndDoc = fwnad fieldsWithName
      where
        fwnad :: [(Name, FC, Plicity, PTerm, Maybe (Docstring (Either Err PTerm)))] -> [(Name, FC, Plicity, PTerm, Docstring (Either Err PTerm))]
        fwnad ((n, nfc, p, t, d) : rest)
          = let doc = fromMaybe emptyDocstring d
            in (n, nfc, p, t, doc) : (fwnad rest)
        fwnad [] = []

elabRecordFunctions :: ElabInfo
                    -> SyntaxInfo
                    -> FC
                    -> Name                                                       -- ^ Record type name
                    -> [(Name, FC, Plicity, PTerm, Docstring (Either Err PTerm))] -- ^ Parameters
                    -> [(Name, FC, Plicity, PTerm, Docstring (Either Err PTerm))] -- ^ Fields
                    -> Name                                                       -- ^ Constructor Name
                    -> PTerm                                                      -- ^ Target type
                    -> Idris ()
elabRecordFunctions info rsyn fc tyn params fields dconName target
  = do logElab 1 $ "Elaborating helper functions for record " ++ show tyn

       logElab 3 $ "Fields: " ++ show fieldNames
       logElab 3 $ "Params: " ++ show paramNames
       -- The elaborated constructor type for the data declaration
       i <- getIState
       ttConsTy <-
         case lookupTyExact dconName (tt_ctxt i) of
               Just as -> return as
               Nothing -> tclift $ tfail $ At fc (Elaborating "record " tyn Nothing (InternalMsg "It seems like the constructor for this record has disappeared. :( \n This is a bug. Please report."))

       -- The arguments to the constructor
       let constructorArgs = getArgTys ttConsTy
       logElab 3 $ "Cons args: " ++ show constructorArgs
       logElab 3 $ "Free fields: " ++ show (filter (not . isFieldOrParam') constructorArgs)
       -- If elaborating the constructor has resulted in some new implicit fields we make projection functions for them.
       let freeFieldsForElab = map (freeField i) (filter (not . isFieldOrParam') constructorArgs)

       -- The parameters for elaboration with their documentation
       -- Parameter functions are all prefixed with "param_".
       let paramsForElab = [((nsroot n), (paramName n), impl, t, d) | (n, _, _, t, d) <- params] -- zipParams i params paramDocs]

       -- The fields (written by the user) with their documentation.
       let userFieldsForElab = [((nsroot n), n, p, t, d) | (n, nfc, p, t, d) <- fields]

       -- All things we need to elaborate projection functions for, together with a number denoting their position in the constructor.
       let projectors = [(n, n', p, t, d, i) | ((n, n', p, t, d), i) <- zip (freeFieldsForElab ++ paramsForElab ++ userFieldsForElab) [0..]]
       -- Build and elaborate projection functions
       elabProj dconName paramNames projectors

       logElab 3 $ "Dependencies: " ++ show fieldDependencies

       logElab 3 $ "Depended on: " ++ show dependedOn

       -- All things we need to elaborate update functions for, together with a number denoting their position in the constructor.
       let updaters = [(n, n', p, t, d, i) | ((n, n', p, t, d), i) <- zip (paramsForElab ++ userFieldsForElab) [0..]]
       -- Build and elaborate update functions
       elabUp dconName paramNames updaters
  where
    -- | Creates a PArg from a plicity and a name where the term is a Placeholder.
    placeholderArg :: Plicity -> Name -> PArg
    placeholderArg p n = asArg p (nsroot n) Placeholder

    -- | Root names of all fields in the current record declarations
    fieldNames :: [Name]
    fieldNames = [nsroot n | (n, _, _, _, _) <- fields]

    paramNames :: [Name]
    paramNames = [nsroot n | (n, _, _, _, _) <- params]

    isFieldOrParam :: Name -> Bool
    isFieldOrParam n = n `elem` (fieldNames ++ paramNames)

    isFieldOrParam' :: (Name, a) -> Bool
    isFieldOrParam' = isFieldOrParam . fst

    isField :: Name -> Bool
    isField = flip elem fieldNames

    isField' :: (Name, a, b, c, d, f) -> Bool
    isField' (n, _, _, _, _, _) = isField n

    fieldTerms :: [PTerm]
    fieldTerms = [t | (_, _, _, t, _) <- fields]

    -- Delabs the TT to PTerm
    -- This is not good.
    -- However, for machine generated implicits, there seems to be no PTerm available.
    -- Is there a better way to do this without building the setters and getters as TT?
    freeField :: IState -> (Name, TT Name) -> (Name, Name, Plicity, PTerm, Docstring (Either Err PTerm))
    freeField i arg = let nameInCons = fst arg -- The name as it appears in the constructor
                          nameFree = expandNS rsyn (freeName $ fst arg) -- The name prefixed with "free_"
                          plicity = impl -- All free fields are implicit as they are machine generated
                          fieldType = delab i (snd arg) -- The type of the field
                          doc = emptyDocstring -- No docmentation for machine generated fields
                      in (nameInCons, nameFree, plicity, fieldType, doc)

    freeName :: Name -> Name
    freeName (UN n) = sUN ("free_" ++ str n)
    freeName (MN i n) = sMN i ("free_" ++ str n)
    freeName (NS n s) = NS (freeName n) s
    freeName n = n

    -- | Zips together parameters with their documentation. If no documentation for a given field exists, an empty docstring is used.
    zipParams :: IState -> [(Name, Plicity, PTerm)] -> [(Name, Docstring (Either Err PTerm))] -> [(Name, PTerm, Docstring (Either Err PTerm))]
    zipParams i ((n, _, t) : rest) ((_, d) : rest') = (n, t, d) : (zipParams i rest rest')
    zipParams i ((n, _, t) : rest) [] = (n, t, emptyDoc) : (zipParams i rest [])
      where emptyDoc = annotCode (tryFullExpr rsyn i) emptyDocstring
    zipParams _ [] [] = []

    paramName :: Name -> Name
    paramName (UN n) = sUN ("param_" ++ str n)
    paramName (MN i n) = sMN i ("param_" ++ str n)
    paramName (NS n s) = NS (paramName n) s
    paramName n = n

    -- | Elaborate the projection functions.
    elabProj :: Name -> [Name] -> [(Name, Name, Plicity, PTerm, Docstring (Either Err PTerm), Int)] -> Idris ()
    elabProj cn paramnames fs
                   = let phArgs = map (uncurry placeholderArg) [(p, n) | (n, _, p, _, _, _) <- fs]
                         elab = \(n, n', p, t, doc, i) ->
                              -- Use projections in types
                           do let t' = projectInType [(m, m') | (m, m', _, _, _, _) <- fs
                                                              -- Parameters are already in scope, so just use them
                                                              , not (m `elem` paramNames)] t
                              elabProjection info n paramnames n' p t' doc rsyn fc target cn phArgs fieldNames i
                     in mapM_ elab fs

    -- | Elaborate the update functions.
    elabUp :: Name -> [Name] -> [(Name, Name, Plicity, PTerm, Docstring (Either Err PTerm), Int)] -> Idris ()
    elabUp cn paramnames fs
                 = let args = map (uncurry asPRefArg) [(p, n) | (n, _, p, _, _, _) <- fs]
                       elab = \(n, n', p, t, doc, i) -> elabUpdate info n paramnames n' p t doc rsyn fc target cn args fieldNames i (optionalSetter n)
                   in mapM_ elab fs

    -- | Decides whether a setter should be generated for a field or not.
    optionalSetter :: Name -> Bool
    optionalSetter n = n `elem` dependedOn

    -- | A map from a field name to the other fields it depends on.
    fieldDependencies :: [(Name, [Name])]
    fieldDependencies = map (uncurry fieldDep) [(n, t) | (n, _, _, t, _) <- fields ++ params]
      where
        fieldDep :: Name -> PTerm -> (Name, [Name])
        fieldDep n t = ((nsroot n), paramNames ++ fieldNames `intersect` allNamesIn t)

    -- | A list of fields depending on another field.
    dependentFields :: [Name]
    dependentFields = filter depends fieldNames
      where
        depends :: Name -> Bool
        depends n = case lookup n fieldDependencies of
                      Just xs -> not $ null xs
                      Nothing -> False

    -- | A list of fields depended on by other fields.
    dependedOn :: [Name]
    dependedOn = concat ((catMaybes (map (\x -> lookup x fieldDependencies) fieldNames)))

-- | Creates and elaborates a projection function.
elabProjection :: ElabInfo
               -> Name                           -- ^ Name of the argument in the constructor
               -> [Name]                         -- ^ Parameter names
               -> Name                           -- ^ Projection Name
               -> Plicity                        -- ^ Projection Plicity
               -> PTerm                          -- ^ Projection Type
               -> (Docstring (Either Err PTerm)) -- ^ Projection Documentation
               -> SyntaxInfo                     -- ^ Projection SyntaxInfo
               -> FC -> PTerm                    -- ^ Projection target type
               -> Name                           -- ^ Data constructor tame
               -> [PArg]                         -- ^ Placeholder Arguments to constructor
               -> [Name]                         -- ^ All Field Names
               -> Int                            -- ^ Argument Index
               -> Idris ()
elabProjection info cname paramnames pname plicity projTy pdoc psyn fc targetTy cn phArgs fnames index
  = do logElab 1 $ "Generating Projection for " ++ show pname

       let ty = generateTy
       logElab 1 $ "Type of " ++ show pname ++ ": " ++ show ty

       let lhs = generateLhs
       logElab 1 $ "LHS of " ++ show pname ++ ": " ++ showTmImpls lhs
       let rhs = generateRhs
       logElab 1 $ "RHS of " ++ show pname ++ ": " ++ showTmImpls rhs

       rec_elabDecl info EAll info ty

       let clause = PClause fc pname lhs [] rhs []
       rec_elabDecl info EAll info $ PClauses fc [] pname [clause]
  where
    -- | The type of the projection function.
    generateTy :: PDecl
    generateTy = PTy pdoc [] psyn fc [] pname NoFC $
                   bindParams paramnames $
                     PPi expl recName NoFC targetTy projTy

    bindParams [] t = t
    bindParams (n : ns) ty = PPi impl n NoFC Placeholder (bindParams ns ty)

    -- | The left hand side of the projection function.
    generateLhs :: PTerm
    generateLhs = let args = lhsArgs index phArgs
                  in PApp fc (PRef fc [] pname) [pexp (PApp fc (PRef fc [] cn) args)]
      where
        lhsArgs :: Int -> [PArg] -> [PArg]
        lhsArgs 0 (_ : rest) = (asArg plicity (nsroot cname) (PRef fc [] pname_in)) : rest
        lhsArgs i (x : rest) = x : (lhsArgs (i-1) rest)
        lhsArgs _ [] = []

    -- | The "_in" name. Used for the lhs.
    pname_in :: Name
    pname_in = rootname -- in_name rootname

    rootname :: Name
    rootname = nsroot cname

    -- | The right hand side of the projection function.
    generateRhs :: PTerm
    generateRhs = PRef fc [] pname_in

-- | Creates and elaborates an update function.
-- If 'optional' is true, we will not fail if we can't elaborate the update function.
elabUpdate :: ElabInfo
           -> Name                           -- ^ Name of the argument in the constructor
           -> [Name]                         -- ^ Parameter names
           -> Name                           -- ^ Field Name
           -> Plicity                        -- ^ Field Plicity
           -> PTerm                          -- ^ Field Type
           -> (Docstring (Either Err PTerm)) -- ^ Field Documentation
           -> SyntaxInfo                     -- ^ Field SyntaxInfo
           -> FC -> PTerm                    -- ^ Projection Source Type
           -> Name                           -- ^ Data Constructor Name
           -> [PArg]                         -- ^ Arguments to constructor
           -> [Name]                         -- ^ All fields
           -> Int                            -- ^ Argument Index
           -> Bool                           -- ^ Optional
           -> Idris ()
elabUpdate info cname paramnames pname plicity pty pdoc psyn fc sty cn args fnames i optional
  = do logElab 1 $ "Generating Update for " ++ show pname

       let ty = generateTy
       logElab 1 $ "Type of " ++ show set_pname ++ ": " ++ show ty

       let lhs = generateLhs
       logElab 1 $ "LHS of " ++ show set_pname ++ ": " ++ showTmImpls lhs

       let rhs = generateRhs
       logElab 1 $ "RHS of " ++ show set_pname ++ ": " ++ showTmImpls rhs

       let clause = PClause fc set_pname lhs [] rhs []

       idrisCatch (do rec_elabDecl info EAll info ty
                      rec_elabDecl info EAll info $ PClauses fc [] set_pname [clause])
         (\err -> logElab 1 $ "Could not generate update function for " ++ show pname)
                  {-if optional
                  then logElab 1 $ "Could not generate update function for " ++ show pname
                  else tclift $ tfail $ At fc (Elaborating "record update function " pname err)) -}
  where
    -- | The type of the update function.
    generateTy :: PDecl
    generateTy = PTy pdoc [] psyn fc [] set_pname NoFC $
                   bindParams paramnames $
                     PPi expl (nsroot pname) NoFC pty $
                       PPi expl recName NoFC sty (substInput sty)
      where substInput = substMatches [(cname, PRef fc [] (nsroot pname))]

    bindParams [] t = t
    bindParams (n : ns) ty = PPi impl n NoFC Placeholder (bindParams ns ty)

    -- | The "_set" name.
    set_pname :: Name
    set_pname = set_name pname

    set_name :: Name -> Name
    set_name (UN n) = sUN ("set_" ++ str n)
    set_name (MN i n) = sMN i ("set_" ++ str n)
    set_name (NS n s) = NS (set_name n) s
    set_name n = n

    -- | The left-hand side of the update function.
    generateLhs :: PTerm
    generateLhs = PApp fc (PRef fc [] set_pname) [pexp $ PRef fc [] pname_in, pexp constructorPattern]
      where
        constructorPattern :: PTerm
        constructorPattern = PApp fc (PRef fc [] cn) args

    -- | The "_in" name.
    pname_in :: Name
    pname_in = in_name rootname

    rootname :: Name
    rootname = nsroot pname

    -- | The right-hand side of the update function.
    generateRhs :: PTerm
    generateRhs = PApp fc (PRef fc [] cn) (newArgs i args)
      where
        newArgs :: Int -> [PArg] -> [PArg]
        newArgs 0 (_ : rest) = (asArg plicity (nsroot cname) (PRef fc [] pname_in)) : rest
        newArgs i (x : rest) = x : (newArgs (i-1) rest)
        newArgs _ [] = []

-- | Post-fixes a name with "_in".
in_name :: Name -> Name
in_name (UN n) = sMN 0 (str n ++ "_in")
in_name (MN i n) = sMN i (str n ++ "_in")
in_name (NS n s) = NS (in_name n) s
in_name n = n

-- | Creates a PArg with a given plicity, name, and term.
asArg :: Plicity -> Name -> PTerm -> PArg
asArg (Imp os _ _ _ _ _) n t = PImp 0 False os n t
asArg (Exp os _ _ _) n t = PExp 0 os n t
asArg (Constraint os _ _) n t = PConstraint 0 os n t
asArg (TacImp os _ s _) n t = PTacImplicit 0 os n s t

-- | Machine name "rec".
recName :: Name
recName = sMN 0 "rec"

recRef = PRef emptyFC [] recName

projectInType :: [(Name, Name)] -> PTerm -> PTerm
projectInType xs = mapPT st
  where
    st :: PTerm -> PTerm
    st (PRef fc hls n)
      | Just pn <- lookup n xs = PApp fc (PRef fc hls pn) [pexp recRef]
    st t = t

-- | Creates an PArg from a plicity and a name where the term is a PRef.
asPRefArg :: Plicity -> Name -> PArg
asPRefArg p n = asArg p (nsroot n) $ PRef emptyFC [] (nsroot n)

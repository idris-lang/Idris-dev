{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Idris.Elab.Record(elabRecord) where

import Idris.AbsSyntax
import Idris.Docstrings
import Idris.Error
import Idris.Delaborate
import Idris.ParseExpr
import Idris.Core.TT
import Idris.Core.Evaluate

import Idris.Elab.Data

import Data.Maybe
import Data.List
import Control.Monad

elabRecord :: ElabInfo ->
              (Docstring (Either Err PTerm)) ->
              SyntaxInfo ->
              FC ->
              DataOpts ->
              Name -> -- ^ Record Type Name
              [(Name, Plicity, PTerm)] -> -- ^ Parameters
              [(Name, Docstring (Either Err PTerm))] -> -- ^ Parameter Docs
              [(Name, Plicity, PTerm)] -> -- ^ Fields
              [(Name, Docstring (Either Err PTerm))] -> -- ^ Field Docs
              Maybe Name -> -- ^ Constructor Name
              (Docstring (Either Err PTerm)) -> -- ^ Constructor Doc
              SyntaxInfo -> -- ^ Constructor SyntaxInfo
              Idris ()
elabRecord info doc rsyn fc opts tyn params paramDocs fields fieldDocs cname cdoc csyn
  = do logLvl 2 $ "Building data declaration for " ++ show tyn
       -- Type constructor
       let tycon = generateTyCon params
       logLvl 4 $ "Type constructor " ++ showTmImpls tycon
       
       -- Data constructor
       dconName <- generateDConName cname 
       let dcon = generateDCon params fields
       logLvl 4 $ "Data constructor: " ++ showTmImpls dcon
       
       -- Build data declaration for elaboration
       let datadecl = PDatadecl tyn tycon [(cdoc, [], dconName, dcon, fc, [])]
       elabData info rsyn doc [] fc opts datadecl

       i <- getIState

       -- The elaborated constructor for the data declaration
       ttCons <-
         case lookupTyExact dconName (tt_ctxt i) of
               Just as -> return as
               Nothing -> tclift $ tfail $ At fc (Elaborating "record" tyn (Msg "It seems like the constructor for this record has disappeared. :( \n This is a bug. Please report."))

       -- The arguments to the constructor
       let constructorArgs = getArgTys ttCons
       -- If elaborating the constructor has resulted in some new implicit fields we make projection functions for them.
       let freeFieldsForElab = map (freeField i) (filter (not . isFieldOrParam') constructorArgs)
           
       -- The parameters for elaboration with their documentation
       let paramsForElab = [((nsroot n), (param_name n), impl, t, d) | (n, t, d) <- zip' i params paramDocs]
           
       -- The fields (written by the user) with their documentation.
       let userFieldsForElab = [((nsroot n), n, p, t, d) | ((n, p, t), (_, d)) <- zip fields fieldDocs]
           
       -- All things we need to elaborate projection functions for, together with a number denoting their position in the constructor.           
       let fieldsForElab = [(n, n', p, t, d, i) | ((n, n', p, t, d), i) <- zip (freeFieldsForElab ++ paramsForElab ++ userFieldsForElab) [0..]]
       
       -- Build projection functions
       elabProj dconName fieldsForElab
       -- Build update functions
       elabUp dconName [(n, n', p, t, d, i) | ((n, n', p, t, d), i) <- zip (paramsForElab ++ userFieldsForElab) [0..]]
  where
    -- | Generates a type constructor.
    generateTyCon :: [(Name, Plicity, PTerm)] -> PTerm
    generateTyCon ((n, p, t) : rest) = PPi p (nsroot n) t (generateTyCon rest)
    generateTyCon [] = PType    

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
    generateDCon :: [(Name, Plicity, PTerm)] -> [(Name, Plicity, PTerm)] -> PTerm
    generateDCon ((n, _, t) : ps) as = PPi impl (nsroot n) t (generateDCon ps as)
    generateDCon [] ((n, p, t) : as) = PPi p    (nsroot n) t (generateDCon [] as)
    generateDCon [] [] = target

    -- | Creates an PArg from a plicity and a name where the term is a PRef.
    paramAsArg :: Plicity -> Name -> PArg
    paramAsArg p n = asArg p (nsroot n) $ PRef fc (nsroot n)

    -- | The target for the constructor and projection functions. Also the source of the update functions.
    target :: PTerm
    target = PApp fc (PRef fc tyn) $ map (uncurry paramAsArg) [(p, n) | (n, p, t) <- params]

    -- | Creates a PArg from a plicity and a name where the term is a Placeholder.
    placeholderArg :: Plicity -> Name -> PArg
    placeholderArg p n = asArg p (nsroot n) Placeholder

    -- | Root names of all fields in the current record declarations
    fieldNames :: [Name]
    fieldNames = [nsroot n | (n, _, _) <- fields]

    paramNames :: [Name]
    paramNames = [nsroot n | (n, _, _) <- params]

    isFieldOrParam :: Name -> Bool
    isFieldOrParam n = n `elem` (fieldNames ++ paramNames)

    isFieldOrParam' :: (Name, a) -> Bool
    isFieldOrParam' = isFieldOrParam . fst

    isField :: Name -> Bool
    isField = flip elem fieldNames

    isField' :: (Name, a, b, c, d, f) -> Bool
    isField' (n, _, _, _, _, _) = isField n

    fieldTerms :: [PTerm]
    fieldTerms = [t | (_, _, t) <- fields]

    projectInType :: [(Name, Name)] -> PTerm -> PTerm
    projectInType xs = mapPT st
      where
        st :: PTerm -> PTerm
        st (PRef fc n)
          | Just pn <- lookup n xs = PApp fc (PRef fc pn) [pexp recRef]
        st t = t

    -- Delabs the TT to PTerm
    -- This is not good.
    -- However, for machine generated implicits, there seems to be no PTerm available.
    -- Is there a better way to do this without building the setters and getters as TT?
    freeField :: IState -> (Name, TT Name) -> (Name, Name, Plicity, PTerm, Docstring (Either Err PTerm))
    freeField i arg = (fst arg, (expandNS rsyn (free_name $ fst arg)), impl, (delab i (snd arg)), emptyDocstring)

    free_name :: Name -> Name
    free_name (UN n) = sUN ("free_" ++ str n)
    free_name (MN i n) = sMN i ("free_" ++ str n)
    free_name (NS n s) = NS (free_name n) s
    free_name n = n
    
    zip' :: IState -> [(Name, Plicity, PTerm)] -> [(Name, Docstring (Either Err PTerm))] -> [(Name, PTerm, Docstring (Either Err PTerm))]
    zip' i ((n, _, t) : rest) ((_, d) : rest') = (n, t, d) : (zip' i rest rest')
    zip' i ((n, _, t) : rest) [] = (n, t, emptyDoc) : (zip' i rest [])
      where emptyDoc = annotCode (tryFullExpr rsyn i) emptyDocstring
    zip' _ [] [] = []

    param_name :: Name -> Name
    param_name (UN n) = sUN ("param_" ++ str n)
    param_name (MN i n) = sMN i ("param_" ++ str n)
    param_name (NS n s) = NS (param_name n) s
    param_name n = n        

    -- | Elaborate the projection functions.
    elabProj :: Name -> [(Name, Name, Plicity, PTerm, Docstring (Either Err PTerm), Int)] -> Idris ()
    elabProj cn fs = let phArgs = map (uncurry placeholderArg) [(p, n) | (n, _, p, _, _, _) <- fs]
                         elab = \(n, n', p, t, doc, i) ->
                           do let t' = projectInType [(m, m') | (m, m', _, _, _, _) <- fs] t
                              elabProjection info n n' p t' doc rsyn fc target cn phArgs fieldNames i
                     in mapM_ elab fs

    -- | Elaborate the update functions.
    elabUp :: Name -> [(Name, Name, Plicity, PTerm, Docstring (Either Err PTerm), Int)] -> Idris ()
    elabUp cn fs = let args = map (uncurry paramAsArg) [(p, n) | (n, _, p, _, _, _) <- fs]
                       elab = \(n, n', p, t, doc, i) -> elabUpdate info n n' p t doc rsyn fc target cn args fieldNames i (optionalSetter n)
                   in mapM_ elab fs

    -- | Decides whether a setter should be generated for a field or not.
    optionalSetter :: Name -> Bool
    optionalSetter n = n `notElem` dependentFields && n `notElem` dependedOn
        
    -- | A map from a field name to the other fields it depends on.
    fieldDependencies :: [(Name, [Name])]
    fieldDependencies = map (uncurry fieldDep) [(n, t) | (n, _, t) <- fields]
      where                           
        fieldDep :: Name -> PTerm -> (Name, [Name])
        fieldDep n t = ((nsroot n), fieldNames `intersect` allNamesIn t)

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
elabProjection :: ElabInfo ->
                  Name -> -- ^ Name of the argument in the constructor
                  Name -> -- ^ Projection Name
                  Plicity -> -- ^ Projection Plicity
                  PTerm -> -- ^ Projection Type
                  (Docstring (Either Err PTerm)) -> -- ^ Projection Documentation
                  SyntaxInfo -> -- ^ Projection SyntaxInfo
                  FC ->
                  PTerm -> -- ^ Projection Target Type
                  Name -> -- ^ Data Constructor Name
                  [PArg] -> -- ^ Placeholder Arguments to constructor
                  [Name] -> -- ^ All Field Names
                  Int -> -- ^ Argument Index
                  Idris ()
elabProjection info cname pname plicity pty pdoc psyn fc tty cn phArgs fnames index
  = do logLvl 2 $ "Generating Projection for " ++ show pname
       
       let ty = generateTy
       logLvl 4 $ "Type of " ++ show pname ++ ": " ++ show ty
       
       let lhs = generateLhs
       logLvl 4 $ "LHS of " ++ show pname ++ ": " ++ showTmImpls lhs
       let rhs = generateRhs
       logLvl 4 $ "RHS of " ++ show pname ++ ": " ++ showTmImpls rhs

       rec_elabDecl info EAll info ty

       let clause = PClause fc pname lhs [] rhs []
       rec_elabDecl info EAll info $ PClauses fc [] pname [clause]
  where
    -- | The type of the projection function.
    generateTy :: PDecl
    generateTy = PTy pdoc [] psyn fc [] pname $ PPi expl recName tty (mapPT applyProjs pty)

    -- | Applies all fields to "rec".
    applyProjs :: PTerm -> PTerm
    applyProjs t@(PRef fc name)
      | (nsroot name) `elem` fnames = PApp fc t [pexp recRef]
    applyProjs t = t

    -- | The left hand side of the projection function.
    generateLhs :: PTerm
    generateLhs = let args = lhsArgs index phArgs
                  in PApp fc (PRef fc pname) [pexp (PApp fc (PRef fc cn) args)]
      where
        lhsArgs :: Int -> [PArg] -> [PArg]
        lhsArgs 0 (_ : rest) = (asArg plicity (nsroot cname) (PRef fc pname_in)) : rest
        lhsArgs i (x : rest) = x : (lhsArgs (i-1) rest)
        lhsArgs _ [] = []

    -- | The "_in" name. Used for the lhs.
    pname_in :: Name
    pname_in = rootname -- in_name rootname

    rootname :: Name
    rootname = nsroot cname

    -- | The right hand side of the projection function.
    generateRhs :: PTerm
    generateRhs = PRef fc pname_in

-- | Creates and elaborates an update function.
-- If 'optional' is true, we will not fail if we can't elaborate the update function.
elabUpdate :: ElabInfo ->
              Name -> -- ^ Name of the argument in the constructor
              Name -> -- ^ Field Name
              Plicity -> -- ^ Field Plicity
              PTerm -> -- ^ Field Type
              (Docstring (Either Err PTerm)) -> -- ^ Field Documentation
              SyntaxInfo -> -- ^ Field SyntaxInfo
              FC ->
              PTerm -> -- ^ Projection Source Type
              Name -> -- ^ Data Constructor Name
              [PArg] -> -- ^ Arguments to constructor
              [Name] -> -- ^ All fields
              Int -> -- ^ Argument Index
              Bool -> -- ^ Optional
              Idris ()
elabUpdate info cname pname plicity pty pdoc psyn fc sty cn args fnames i optional
  = do logLvl 2 $ "Generating Update for " ++ show pname
       
       let ty = generateTy
       logLvl 4 $ "Type of " ++ show set_pname ++ ": " ++ show ty
       
       let lhs = generateLhs
       logLvl 4 $ "LHS of " ++ show set_pname ++ ": " ++ showTmImpls lhs
       
       let rhs = generateRhs
       logLvl 4 $ "RHS of " ++ show set_pname ++ ": " ++ showTmImpls rhs

       let clause = PClause fc set_pname lhs [] rhs []       

       idrisCatch (do rec_elabDecl info EAll info ty
                      rec_elabDecl info EAll info $ PClauses fc [] set_pname [clause])
         (\err -> if optional
                  then logLvl 2 $ "Could not generate update function for " ++ show pname
                  else tclift $ tfail $ At fc (Elaborating "record update function" pname err))
  where
    -- | The type of the udpate function.
    generateTy :: PDecl
    generateTy = PTy pdoc [] psyn fc [] set_pname $ PPi expl (nsroot pname) pty (PPi expl recName sty (substInput sty))
      where substInput = substMatches [(cname, PRef fc (nsroot pname))]

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
    generateLhs = PApp fc (PRef fc set_pname) [pexp $ PRef fc pname_in, pexp constructorPattern]
      where
        constructorPattern :: PTerm
        constructorPattern = PApp fc (PRef fc cn) args

    -- | The "_in" name.
    pname_in :: Name
    pname_in = in_name rootname

    rootname :: Name
    rootname = nsroot pname

    -- | The right-hand side of the update function.
    generateRhs :: PTerm
    generateRhs = PApp fc (PRef fc cn) (newArgs i args)
      where
        newArgs :: Int -> [PArg] -> [PArg]
        newArgs 0 (_ : rest) = (asArg plicity (nsroot cname) (PRef fc pname_in)) : rest
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
asArg (Imp os _ _ _) n t = PImp 0 False os n t
asArg (Exp os _ _) n t = PExp 0 os n t
asArg (Constraint os _) n t = PConstraint 0 os n t
asArg (TacImp os _ s) n t = PTacImplicit 0 os n s t

-- | Machine name "rec".
recName :: Name
recName = sMN 0 "rec"

recRef = PRef emptyFC recName

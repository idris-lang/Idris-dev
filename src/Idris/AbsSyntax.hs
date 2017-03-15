{-|
Module      : Idris.AbsSyntax
Description : Provides Idris' core data definitions and utility code.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE DeriveFunctor, PatternGuards #-}

module Idris.AbsSyntax(
    module Idris.AbsSyntax
  , module Idris.AbsSyntaxTree
  ) where

import Idris.AbsSyntaxTree
import Idris.Colours
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Docstrings
import Idris.IdeMode hiding (Opt(..))
import IRTS.CodegenCommon

import System.Directory (canonicalizePath, doesFileExist)
import System.IO

import Control.Applicative
import Control.Monad.State
import Prelude hiding (Applicative, Foldable, Traversable, (<$>))

import Data.Either
import Data.List hiding (insert, union)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import System.IO.Error (tryIOError)

import Data.Generics.Uniplate.Data (descend, descendM)

import Debug.Trace
import Util.DynamicLinker
import Util.Pretty
import Util.System

getContext :: Idris Context
getContext = do i <- getIState; return (tt_ctxt i)

forCodegen :: Codegen -> [(Codegen, a)] -> [a]
forCodegen tgt xs = [x | (tgt', x) <- xs, eqLang tgt tgt']
    where
        eqLang (Via _ x) (Via _ y) = x == y
        eqLang Bytecode Bytecode = True
        eqLang _ _ = False

getObjectFiles :: Codegen -> Idris [FilePath]
getObjectFiles tgt = do i <- getIState; return (forCodegen tgt $ idris_objs i)

addObjectFile :: Codegen -> FilePath -> Idris ()
addObjectFile tgt f = do i <- getIState; putIState $ i { idris_objs = nub $ (tgt, f) : idris_objs i }

getLibs :: Codegen -> Idris [String]
getLibs tgt = do i <- getIState; return (forCodegen tgt $ idris_libs i)

addLib :: Codegen -> String -> Idris ()
addLib tgt f = do i <- getIState; putIState $ i { idris_libs = nub $ (tgt, f) : idris_libs i }

getFlags :: Codegen -> Idris [String]
getFlags tgt = do i <- getIState; return (forCodegen tgt $ idris_cgflags i)

addFlag :: Codegen -> String -> Idris ()
addFlag tgt f = do i <- getIState; putIState $ i { idris_cgflags = nub $ (tgt, f) : idris_cgflags i }

addDyLib :: [String] -> Idris (Either DynamicLib String)
addDyLib libs = do i <- getIState
                   let ls = idris_dynamic_libs i
                   let importdirs = opt_importdirs (idris_options i)
                   case mapMaybe (findDyLib ls) libs of
                     x:_ -> return (Left x)
                     [] -> do
                       handle <- lift . lift .
                                 mapM (\l -> catchIO (tryLoadLib importdirs l)
                                                     (\_ -> return Nothing)) $ libs
                       case msum handle of
                         Nothing -> return (Right $ "Could not load dynamic alternatives \"" ++
                                                    intercalate "," libs ++ "\"")
                         Just x -> do putIState $ i { idris_dynamic_libs = x:ls }
                                      return (Left x)
    where findDyLib :: [DynamicLib] -> String -> Maybe DynamicLib
          findDyLib []         _                     = Nothing
          findDyLib (lib:libs') l | l == lib_name lib = Just lib
                                  | otherwise         = findDyLib libs' l

getAutoImports :: Idris [FilePath]
getAutoImports = do i <- getIState
                    return (opt_autoImport (idris_options i))

addAutoImport :: FilePath -> Idris ()
addAutoImport fp = do i <- getIState
                      let opts = idris_options i
                      put (i { idris_options = opts { opt_autoImport =
                                                       fp : opt_autoImport opts } } )

addDefinedName :: Name -> Idris ()
addDefinedName n = do ist <- getIState
                      putIState $ ist { idris_inmodule = S.insert n (idris_inmodule ist) }

getDefinedNames :: Idris [Name]
getDefinedNames = do ist <- getIState
                     return (S.toList (idris_inmodule ist))

addTT :: Term -> Idris (Maybe Term)
addTT t = do ist <- getIState
             case M.lookup t (idris_ttstats ist) of
                  Nothing -> do let tt' = M.insert t (1, t) (idris_ttstats ist)
                                putIState $ ist { idris_ttstats = tt' }
                                return Nothing
                  Just (i, t') -> do let tt' = M.insert t' (i + 1, t') (idris_ttstats ist)
                                     putIState $ ist { idris_ttstats = tt' }
                                     return (Just t')

dumpTT :: Idris ()
dumpTT = do ist <- get
            let sts = sortBy count (M.toList (idris_ttstats ist))
            mapM_ dump sts
            return ()
  where
    count (_,x) (_,y) = compare y x
    dump (tm, val) = runIO $ putStrLn (show val ++ ": " ++ show tm)

addHdr :: Codegen -> String -> Idris ()
addHdr tgt f = do i <- getIState; putIState $ i { idris_hdrs = nub $ (tgt, f) : idris_hdrs i }

addImported :: Bool -> FilePath -> Idris ()
addImported pub f
     = do i <- getIState
          putIState $ i { idris_imported = nub $ (f, pub) : idris_imported i }

addLangExt :: LanguageExt -> Idris ()
addLangExt e = do i <- getIState
                  putIState $ i {
                    idris_language_extensions = e : idris_language_extensions i
                  }

-- | Transforms are organised by the function being applied on the lhs
-- of the transform, to make looking up appropriate transforms quicker
addTrans :: Name -> (Term, Term) -> Idris ()
addTrans basefn t
           = do i <- getIState
                let t' = case lookupCtxtExact basefn (idris_transforms i) of
                              Just def -> (t : def)
                              Nothing -> [t]
                putIState $ i { idris_transforms = addDef basefn t'
                                                          (idris_transforms i) }

-- | Add transformation rules from a definition, which will reverse the
-- definition for an error to make it more readable
addErrRev :: (Term, Term) -> Idris ()
addErrRev t = do i <- getIState
                 putIState $ i { idris_errRev = t : idris_errRev i }

-- | Say that the name should always be reduced in error messages, to
-- help readability/error reflection
addErrReduce :: Name -> Idris ()
addErrReduce t = do i <- getIState
                    putIState $ i { idris_errReduce = t : idris_errReduce i }

addErasureUsage :: Name -> Int -> Idris ()
addErasureUsage n i = do ist <- getIState
                         putIState $ ist { idris_erasureUsed = (n, i) : idris_erasureUsed ist }

addExport :: Name -> Idris ()
addExport n = do ist <- getIState
                 putIState $ ist { idris_exports = n : idris_exports ist }

addUsedName :: FC -> Name -> Name -> Idris ()
addUsedName fc n arg
    = do ist <- getIState
         case lookupTyName n (tt_ctxt ist) of
              [(n', ty)] -> addUsage n' 0 ty
              [] -> throwError (At fc (NoSuchVariable n))
              xs -> throwError (At fc (CantResolveAlts (map fst xs)))
  where addUsage n i (Bind x _ sc) | x == arg = do addIBC (IBCUsage (n, i))
                                                   addErasureUsage n i
                                   | otherwise = addUsage n (i + 1) sc
        addUsage _ _ _ = throwError (At fc (Msg ("No such argument name " ++ show arg)))

getErasureUsage :: Idris [(Name, Int)]
getErasureUsage = do ist <- getIState;
                     return (idris_erasureUsed ist)

getExports :: Idris [Name]
getExports = do ist <- getIState
                return (idris_exports ist)

totcheck :: (FC, Name) -> Idris ()
totcheck n = do i <- getIState; putIState $ i { idris_totcheck = idris_totcheck i ++ [n] }

defer_totcheck :: (FC, Name) -> Idris ()
defer_totcheck n
   = do i <- getIState;
        putIState $ i { idris_defertotcheck = nub (idris_defertotcheck i ++ [n]) }

clear_totcheck :: Idris ()
clear_totcheck  = do i <- getIState; putIState $ i { idris_totcheck = [] }

setFlags :: Name -> [FnOpt] -> Idris ()
setFlags n fs = do i <- getIState; putIState $ i { idris_flags = addDef n fs (idris_flags i) }

addFnOpt :: Name -> FnOpt -> Idris ()
addFnOpt n f = do i <- getIState
                  let fls = case lookupCtxtExact n (idris_flags i) of
                                 Nothing -> []
                                 Just x -> x
                  setFlags n (f : fls)

setFnInfo :: Name -> FnInfo -> Idris ()
setFnInfo n fs = do i <- getIState; putIState $ i { idris_fninfo = addDef n fs (idris_fninfo i) }

setAccessibility :: Name -> Accessibility -> Idris ()
setAccessibility n a
         = do i <- getIState
              let ctxt = setAccess n a (tt_ctxt i)
              putIState $ i { tt_ctxt = ctxt }

-- | get the accessibility of a name outside this module
getFromHideList :: Name -> Idris (Maybe Accessibility)
getFromHideList n = do i <- getIState
                       return $ lookupCtxtExact n (hide_list i)

setTotality :: Name -> Totality -> Idris ()
setTotality n a
         = do i <- getIState
              let ctxt = setTotal n a (tt_ctxt i)
              putIState $ i { tt_ctxt = ctxt }

setInjectivity :: Name -> Injectivity -> Idris ()
setInjectivity n a
         = do i <- getIState
              let ctxt = setInjective n a (tt_ctxt i)
              putIState $ i { tt_ctxt = ctxt }

getTotality :: Name -> Idris Totality
getTotality n
         = do i <- getIState
              case lookupTotal n (tt_ctxt i) of
                [t] -> return t
                _ -> return (Total [])

-- Get coercions which might return the required type
getCoercionsTo :: IState -> Type -> [Name]
getCoercionsTo i ty =
    let cs = idris_coercions i
        (fn,_) = unApply (getRetTy ty) in
        findCoercions fn cs
    where findCoercions _ [] = []
          findCoercions t (n : ns) =
             let ps = case lookupTy n (tt_ctxt i) of
                        [ty'] -> case unApply (getRetTy (normalise (tt_ctxt i) [] ty')) of
                                   (t', _) -> [n | t == t']
                        _ -> [] in
                 ps ++ findCoercions t ns

addToCG :: Name -> CGInfo -> Idris ()
addToCG n cg
   = do i <- getIState
        putIState $ i { idris_callgraph = addDef n cg (idris_callgraph i) }

addCalls :: Name -> [Name] -> Idris ()
addCalls n calls
   = do i <- getIState
        case lookupCtxtExact n (idris_callgraph i) of
             Nothing -> addToCG n (CGInfo calls Nothing [] [])
             Just (CGInfo cs ans scg used) ->
                addToCG n (CGInfo (nub (calls ++ cs)) ans scg used)

addTyInferred :: Name -> Idris ()
addTyInferred n
   = do i <- getIState
        putIState $ i { idris_tyinfodata =
                        addDef n TIPartial (idris_tyinfodata i) }

addTyInfConstraints :: FC -> [(Term, Term)] -> Idris ()
addTyInfConstraints fc ts = do logLvl 2 $ "TI missing: " ++ show ts
                               mapM_ addConstraint ts
                               return ()
    where addConstraint (x, y) = findMVApps x y

          findMVApps x y
             = do let (fx, argsx) = unApply x
                  let (fy, argsy) = unApply y
                  if (fx /= fy)
                     then do
                       tryAddMV fx y
                       tryAddMV fy x
                     else mapM_ addConstraint (zip argsx argsy)

          tryAddMV (P _ mv _) y =
               do ist <- get
                  case lookup mv (idris_metavars ist) of
                       Just _ -> addConstraintRule mv y
                       _ -> return ()
          tryAddMV _ _ = return ()

          addConstraintRule :: Name -> Term -> Idris ()
          addConstraintRule n t
             = do ist <- get
                  logLvl 1 $ "TI constraint: " ++ show (n, t)
                  case lookupCtxt n (idris_tyinfodata ist) of
                     [TISolution ts] ->
                         do mapM_ (checkConsistent t) ts
                            let ti' = addDef n (TISolution (t : ts))
                                               (idris_tyinfodata ist)
                            put $ ist { idris_tyinfodata = ti' }
                     _ ->
                         do let ti' = addDef n (TISolution [t])
                                               (idris_tyinfodata ist)
                            put $ ist { idris_tyinfodata = ti' }

          -- Check a solution is consistent with previous solutions
          -- Meaning: If heads are both data types, they had better be the
          -- same.
          checkConsistent :: Term -> Term -> Idris ()
          checkConsistent x y =
              do let (fx, _) = unApply x
                 let (fy, _) = unApply y
                 case (fx, fy) of
                      (P (TCon _ _) n _, P (TCon _ _) n' _) -> errWhen (n/=n')
                      (P (TCon _ _) n _, Constant _) -> errWhen True
                      (Constant _, P (TCon _ _) n' _) -> errWhen True
                      (P (DCon _ _ _) n _, P (DCon _ _ _) n' _) -> errWhen (n/=n')
                      _ -> return ()

              where errWhen True
                       = throwError (At fc
                            (CantUnify False (x, Nothing) (y, Nothing) (Msg "") [] 0))
                    errWhen False = return ()

isTyInferred :: Name -> Idris Bool
isTyInferred n
   = do i <- getIState
        case lookupCtxt n (idris_tyinfodata i) of
             [TIPartial] -> return True
             _ -> return False

-- | Adds error handlers for a particular function and argument. If
-- names are ambiguous, all matching handlers are updated.
addFunctionErrorHandlers :: Name -> Name -> [Name] -> Idris ()
addFunctionErrorHandlers f arg hs =
 do i <- getIState
    let oldHandlers = idris_function_errorhandlers i
    let newHandlers = flip (addDef f) oldHandlers $
                      case lookupCtxtExact f oldHandlers of
                        Nothing            -> M.singleton arg (S.fromList hs)
                        Just (oldHandlers) -> M.insertWith S.union arg (S.fromList hs) oldHandlers
                        -- will always be one of those two, thus no extra case
    putIState $ i { idris_function_errorhandlers = newHandlers }

-- | Trace all the names in a call graph starting at the given name
getAllNames :: Name -> Idris [Name]
getAllNames n = do i <- getIState
                   case getCGAllNames i n of
                        Just ns -> return ns
                        Nothing -> do ns <- allNames [] n
                                      addCGAllNames i n ns
                                      return ns

getCGAllNames :: IState -> Name -> Maybe [Name]
getCGAllNames i n = case lookupCtxtExact n (idris_callgraph i) of
                         Just ci -> allCalls ci
                         _ -> Nothing

addCGAllNames :: IState -> Name -> [Name] -> Idris ()
addCGAllNames i n ns
      = case lookupCtxtExact n (idris_callgraph i) of
             Just ci -> addToCG n (ci { allCalls = Just ns })
             _ -> addToCG n (CGInfo [] (Just ns) [] [])

allNames :: [Name] -> Name -> Idris [Name]
allNames ns n | n `elem` ns = return []
allNames ns n = do i <- getIState
                   case getCGAllNames i n of
                        Just ns -> return ns
                        Nothing -> case lookupCtxtExact n (idris_callgraph i) of
                                        Just ci ->
                                          do more <- mapM (allNames (n:ns)) (calls ci)
                                             let ns' = nub (n : concat more)
                                             addCGAllNames i n ns'
                                             return ns'
                                        _ -> return [n]

addCoercion :: Name -> Idris ()
addCoercion n = do i <- getIState
                   putIState $ i { idris_coercions = nub $ n : idris_coercions i }

addDocStr :: Name -> Docstring DocTerm -> [(Name, Docstring DocTerm)] -> Idris ()
addDocStr n doc args
   = do i <- getIState
        putIState $ i { idris_docstrings = addDef n (doc, args) (idris_docstrings i) }

addNameHint :: Name -> Name -> Idris ()
addNameHint ty n
   = do i <- getIState
        ty' <- case lookupCtxtName ty (idris_implicits i) of
                       [(tyn, _)] -> return tyn
                       [] -> throwError (NoSuchVariable ty)
                       tyns -> throwError (CantResolveAlts (map fst tyns))
        let ns' = case lookupCtxt ty' (idris_namehints i) of
                       [ns] -> ns ++ [n]
                       _ -> [n]
        putIState $ i { idris_namehints = addDef ty' ns' (idris_namehints i) }

getNameHints :: IState -> Name -> [Name]
getNameHints _ (UN arr) | arr == txt "->" = [sUN "f",sUN "g"]
getNameHints i n =
        case lookupCtxt n (idris_namehints i) of
             [ns] -> ns
             _ -> []

addDeprecated :: Name -> String -> Idris ()
addDeprecated n reason = do
  i <- getIState
  putIState $ i { idris_deprecated = addDef n reason (idris_deprecated i) }

getDeprecated :: Name -> Idris (Maybe String)
getDeprecated n = do
  i <- getIState
  return $ lookupCtxtExact n (idris_deprecated i)

addFragile :: Name -> String -> Idris ()
addFragile n reason = do
  i <- getIState
  putIState $ i { idris_fragile = addDef n reason (idris_fragile i) }

getFragile :: Name -> Idris (Maybe String)
getFragile n = do
  i <- getIState
  return $ lookupCtxtExact n (idris_fragile i)

push_estack :: Name -> Bool -> Idris ()
push_estack n implementation
    = do i <- getIState
         putIState (i { elab_stack = (n, implementation) : elab_stack i })

pop_estack :: Idris ()
pop_estack = do i <- getIState
                putIState (i { elab_stack = ptail (elab_stack i) })
    where ptail [] = []
          ptail (_ : xs) = xs

-- | Add an interface implementation function.
--
-- Precondition: the implementation should have the correct type.
--
-- Dodgy hack 1: Put integer implementations first in the list so they are
-- resolved by default.
--
-- Dodgy hack 2: put constraint chasers (ParentN) last
addImplementation :: Bool -- ^ whether the name is an Integer implementation
                  -> Bool -- ^ whether to include the implementation in implementation search
                  -> Name -- ^ the name of the interface
                  -> Name -- ^ the name of the implementation
                  -> Idris ()
addImplementation int res n i
    = do ist <- getIState
         case lookupCtxt n (idris_interfaces ist) of
                [CI a b c d e f g ins fds] ->
                     do let cs = addDef n (CI a b c d e f g (addI i ins) fds) (idris_interfaces ist)
                        putIState $ ist { idris_interfaces = cs }
                _ -> do let cs = addDef n (CI (sMN 0 "none") [] [] [] [] [] [] [(i, res)] []) (idris_interfaces ist)
                        putIState $ ist { idris_interfaces = cs }
  where addI, insI :: Name -> [(Name, Bool)] -> [(Name, Bool)]
        addI i ins | int = (i, res) : ins
                   | chaser n = ins ++ [(i, res)]
                   | otherwise = insI i ins
        insI i [] = [(i, res)]
        insI i (n : ns) | chaser (fst n) = (i, res) : n : ns
                        | otherwise = n : insI i ns

        chaser (SN (ParentN _ _)) = True
        chaser (NS n _) = chaser n
        chaser _ = False

-- | Add a privileged implementation - one which implementation search will
-- happily resolve immediately if it is type correct This is used for
-- naming parent implementations when defining an implementation with
-- constraints.  Returns the old list, so we can revert easily at the
-- end of a block
addOpenImpl :: [Name] -> Idris [Name]
addOpenImpl ns = do ist <- getIState
                    ns' <- mapM (checkValid ist) ns
                    let open = idris_openimpls ist
                    putIState $ ist { idris_openimpls = nub (ns' ++ open) }
                    return open
  where
    checkValid ist n
      = case lookupCtxtName n (idris_implicits ist) of
             [(n', _)] -> return n'
             []        -> throwError (NoSuchVariable n)
             more      -> throwError (CantResolveAlts (map fst more))

setOpenImpl :: [Name] -> Idris ()
setOpenImpl ns = do ist <- getIState
                    putIState $ ist { idris_openimpls = ns }

getOpenImpl :: Idris [Name]
getOpenImpl = do ist <- getIState
                 return (idris_openimpls ist)

addInterface :: Name -> InterfaceInfo -> Idris ()
addInterface n i
   = do ist <- getIState
        let i' = case lookupCtxt n (idris_interfaces ist) of
                      [c] -> i { interface_implementations = interface_implementations c ++
                                                             interface_implementations i }
                      _ -> i
        putIState $ ist { idris_interfaces = addDef n i' (idris_interfaces ist) }

updateIMethods :: Name -> [(Name, PTerm)] -> Idris ()
updateIMethods n meths
   = do ist <- getIState
        let i = case lookupCtxtExact n (idris_interfaces ist) of
                     Just c -> c { interface_methods = update (interface_methods c) }
                     Nothing -> error "Can't happen updateIMethods"
        putIState $ ist { idris_interfaces = addDef n i (idris_interfaces ist) }
  where
    update [] = []
    update (m@(n, (b, opts, t)) : rest)
        | Just ty <- lookup n meths
             = (n, (b, opts, ty)) : update rest
        | otherwise = m : update rest

addRecord :: Name -> RecordInfo -> Idris ()
addRecord n ri = do ist <- getIState
                    putIState $ ist { idris_records = addDef n ri (idris_records ist) }

addAutoHint :: Name -> Name -> Idris ()
addAutoHint n hint =
    do ist <- getIState
       case lookupCtxtExact n (idris_autohints ist) of
            Nothing ->
                 do let hs = addDef n [hint] (idris_autohints ist)
                    putIState $ ist { idris_autohints = hs }
            Just nhints ->
                 do let hs = addDef n (hint : nhints) (idris_autohints ist)
                    putIState $ ist { idris_autohints = hs }

getAutoHints :: Name -> Idris [Name]
getAutoHints n = do ist <- getIState
                    case lookupCtxtExact n (idris_autohints ist) of
                         Nothing -> return []
                         Just ns -> return ns

addIBC :: IBCWrite -> Idris ()
addIBC ibc@(IBCDef n)
           = do i <- getIState
                when (notDef (ibc_write i)) $
                  putIState $ i { ibc_write = ibc : ibc_write i }
   where notDef [] = True
         notDef (IBCDef n': _) | n == n' = False
         notDef (_ : is) = notDef is
addIBC ibc = do i <- getIState; putIState $ i { ibc_write = ibc : ibc_write i }

clearIBC :: Idris ()
clearIBC = do i <- getIState; putIState $ i { ibc_write = [],
                                              idris_inmodule = S.empty }

resetNameIdx :: Idris ()
resetNameIdx = do i <- getIState
                  put (i { idris_nameIdx = (0, emptyContext) })

-- | Used to preserve sharing of names
addNameIdx :: Name -> Idris (Int, Name)
addNameIdx n = do i <- getIState
                  let (i', x) = addNameIdx' i n
                  putIState i'
                  return x

addNameIdx' :: IState -> Name -> (IState, (Int, Name))
addNameIdx' i n
   = let idxs = snd (idris_nameIdx i) in
         case lookupCtxt n idxs of
            [x] -> (i, x)
            _ -> let i' = fst (idris_nameIdx i) + 1 in
                    (i { idris_nameIdx = (i', addDef n (i', n) idxs) }, (i', n))

getSymbol :: Name -> Idris Name
getSymbol n = do i <- getIState
                 case M.lookup n (idris_symbols i) of
                      Just n' -> return n'
                      Nothing -> do let sym' = M.insert n n (idris_symbols i)
                                    put (i { idris_symbols = sym' })
                                    return n

getHdrs :: Codegen -> Idris [String]
getHdrs tgt = do i <- getIState; return (forCodegen tgt $ idris_hdrs i)

getImported ::  Idris [(FilePath, Bool)]
getImported = do i <- getIState; return (idris_imported i)

setErrSpan :: FC -> Idris ()
setErrSpan x = do i <- getIState;
                  case (errSpan i) of
                      Nothing -> putIState $ i { errSpan = Just x }
                      Just _ -> return ()

clearErr :: Idris ()
clearErr = do i <- getIState
              putIState $ i { errSpan = Nothing }

getSO :: Idris (Maybe String)
getSO = do i <- getIState
           return (compiled_so i)

setSO :: Maybe String -> Idris ()
setSO s = do i <- getIState
             putIState (i { compiled_so = s })

getIState :: Idris IState
getIState = get

putIState :: IState -> Idris ()
putIState = put

updateIState :: (IState -> IState) -> Idris ()
updateIState f = do i <- getIState
                    putIState $ f i

withContext :: (IState -> Ctxt a) -> Name -> b -> (a -> Idris b) -> Idris b
withContext ctx name dflt action = do
    ist <- getIState
    case lookupCtxt name (ctx ist) of
        [x] -> action x
        _   -> return dflt

withContext_ :: (IState -> Ctxt a) -> Name -> (a -> Idris ()) -> Idris ()
withContext_ ctx name action = withContext ctx name () action

-- | A version of liftIO that puts errors into the exception type of
-- the Idris monad
runIO :: IO a -> Idris a
runIO x = liftIO (tryIOError x) >>= either (throwError . Msg . show) return
-- TODO: create specific Idris exceptions for specific IO errors such as "openFile: does not exist"
--
-- Issue #1738 on the issue tracker.
--     https://github.com/idris-lang/Idris-dev/issues/1738

getName :: Idris Int
getName = do i <- getIState;
             let idx = idris_name i;
             putIState (i { idris_name = idx + 1 })
             return idx

-- | InternalApp keeps track of the real function application for
-- making case splits from, not the application the programmer wrote,
-- which doesn't have the whole context in any case other than top
-- level definitions
addInternalApp :: FilePath -> Int -> PTerm -> Idris ()
addInternalApp fp l t
    = do i <- getIState
         -- We canonicalise the path to make "./Test/Module.idr" equal
         -- to "Test/Module.idr"
         exists <- runIO $ doesFileExist fp
         when exists $
           do fp' <- runIO $ canonicalizePath fp
              putIState (i { idris_lineapps = ((fp', l), t) : idris_lineapps i })

getInternalApp :: FilePath -> Int -> Idris PTerm
getInternalApp fp l = do i <- getIState
                         -- We canonicalise the path to make
                         -- "./Test/Module.idr" equal to
                         -- "Test/Module.idr"
                         exists <- runIO $ doesFileExist fp
                         if exists
                           then do fp' <- runIO $ canonicalizePath fp
                                   case lookup (fp', l) (idris_lineapps i) of
                                     Just n' -> return n'
                                     Nothing -> return Placeholder
                                     -- TODO: What if it's not there?
                           else return Placeholder

-- | Pattern definitions are only used for coverage checking, so erase
-- them when we're done
clearOrigPats :: Idris ()
clearOrigPats = do i <- get
                   let ps = idris_patdefs i
                   let ps' = mapCtxt (\ (_,miss) -> ([], miss)) ps
                   put (i { idris_patdefs = ps' })

-- | Erase types from Ps in the context (basically ending up with
-- what's in the .ibc, which is all we need after all the analysis is
-- done)
clearPTypes :: Idris ()
clearPTypes = do i <- get
                 let ctxt = tt_ctxt i
                 put (i { tt_ctxt = mapDefCtxt pErase ctxt })
   where pErase (CaseOp c t tys orig _ cds)
            = CaseOp c t tys orig [] (pErase' cds)
         pErase x = x
         pErase' (CaseDefs (cs, c) rs)
             = let c' = (cs, fmap pEraseType c) in
                   CaseDefs c' rs

checkUndefined :: FC -> Name -> Idris ()
checkUndefined fc n
    = do i <- getContext
         case lookupTy n i of
             (_:_)  -> throwError . Msg $ show fc ++ ":" ++
                                          show n ++ " already defined"
             _ -> return ()

isUndefined :: FC -> Name -> Idris Bool
isUndefined _ n
    = do i <- getContext
         case lookupTyExact n i of
             Just _ -> return False
             _ -> return True

setContext :: Context -> Idris ()
setContext ctxt = do i <- getIState; putIState (i { tt_ctxt = ctxt } )

updateContext :: (Context -> Context) -> Idris ()
updateContext f = do i <- getIState; putIState (i { tt_ctxt = f (tt_ctxt i) } )

addConstraints :: FC -> (Int, [UConstraint]) -> Idris ()
addConstraints fc (v, cs)
    = do tit <- typeInType
         when (not tit) $ do
             i <- getIState
             let ctxt = tt_ctxt i
             let ctxt' = ctxt { next_tvar = v }
             let ics = insertAll (zip cs (repeat fc)) (idris_constraints i)
             putIState $ i { tt_ctxt = ctxt', idris_constraints = ics }
  where
    insertAll [] c = c
    insertAll ((ULE (UVal 0) _, fc) : cs) ics = insertAll cs ics
    insertAll ((ULE x y, fc) : cs) ics | x == y = insertAll cs ics
    insertAll ((c, fc) : cs) ics
       = insertAll cs $ S.insert (ConstraintFC c fc) ics

addDeferred = addDeferred' Ref
addDeferredTyCon = addDeferred' (TCon 0 0)

-- | Save information about a name that is not yet defined
addDeferred' :: NameType
             -> [(Name, (Int, Maybe Name, Type, [Name], Bool, Bool))]
                -- ^ The Name is the name being made into a metavar,
                -- the Int is the number of vars that are part of a
                -- putative proof context, the Maybe Name is the
                -- top-level function containing the new metavariable,
                -- the Type is its type, and the Bool is whether :p is
                -- allowed
             -> Idris ()
addDeferred' nt ns
  = do mapM_ (\(n, (i, _, t, _, _, _)) -> updateContext (addTyDecl n nt (tidyNames S.empty t))) ns
       mapM_ (\(n, _) -> when (not (n `elem` primDefs)) $ addIBC (IBCMetavar n)) ns
       i <- getIState
       putIState $ i { idris_metavars = map (\(n, (i, top, _, ns, isTopLevel, isDefinable)) ->
                                                  (n, (top, i, ns, isTopLevel, isDefinable))) ns ++
                                            idris_metavars i }
  where
        -- 'tidyNames' is to generate user accessible names in case they are
        -- needed in tactic scripts
        tidyNames used (Bind (MN i x) b sc)
            = let n' = uniqueNameSet (UN x) used in
                  Bind n' b $ tidyNames (S.insert n' used) sc
        tidyNames used (Bind n b sc)
            = let n' = uniqueNameSet n used in
                  Bind n' b $ tidyNames (S.insert n' used) sc
        tidyNames _    b = b

solveDeferred :: FC -> Name -> Idris ()
solveDeferred fc n
    = do i <- getIState
         case lookup n (idris_metavars i) of
              Just (_, _, _, _, False) ->
                   throwError $ At fc $ Msg ("Can't define hole " ++ show n ++ " as it depends on other holes")
              _ -> putIState $ i { idris_metavars =
                                       filter (\(n', _) -> n/=n')
                                          (idris_metavars i),
                                     ibc_write =
                                       filter (notMV n) (ibc_write i)
                                          }
    where notMV n (IBCMetavar n') = not (n == n')
          notMV n _ = True

getUndefined :: Idris [Name]
getUndefined = do i <- getIState
                  return (map fst (idris_metavars i) \\ primDefs)

isMetavarName :: Name -> IState -> Bool
isMetavarName n ist
     = case lookupNames n (tt_ctxt ist) of
            (t:_) -> isJust $ lookup t (idris_metavars ist)
            _     -> False

getWidth :: Idris ConsoleWidth
getWidth = fmap idris_consolewidth getIState

setWidth :: ConsoleWidth -> Idris ()
setWidth w = do ist <- getIState
                put ist { idris_consolewidth = w }

setDepth :: Maybe Int -> Idris ()
setDepth d = do ist <- getIState
                put ist { idris_options = (idris_options ist) { opt_printdepth = d } }

typeDescription :: String
typeDescription = "The type of types"


type1Doc :: Doc OutputAnnotation
type1Doc = (annotate (AnnType "Type" "The type of types, one level up") $ text "Type 1")


isetPrompt :: String -> Idris ()
isetPrompt p = do i <- getIState
                  case idris_outputmode i of
                    IdeMode n h -> runIO . hPutStrLn h $ convSExp "set-prompt" p n

-- | Tell clients how much was parsed and loaded
isetLoadedRegion :: Idris ()
isetLoadedRegion = do i <- getIState
                      let span = idris_parsedSpan i
                      case span of
                        Just fc ->
                          case idris_outputmode i of
                            IdeMode n h ->
                              runIO . hPutStrLn h $
                                convSExp "set-loaded-region" fc n
                        Nothing -> return ()

setLogLevel :: Int -> Idris ()
setLogLevel l = do i <- getIState
                   let opts = idris_options i
                   let opt' = opts { opt_logLevel = l }
                   putIState $ i { idris_options = opt' }

setLogCats :: [LogCat] -> Idris ()
setLogCats cs = do
  i <- getIState
  let opts = idris_options i
  let opt' = opts { opt_logcats = cs }
  putIState $ i { idris_options = opt' }

setCmdLine :: [Opt] -> Idris ()
setCmdLine opts = do i <- getIState
                     let iopts = idris_options i
                     putIState $ i { idris_options = iopts { opt_cmdline = opts } }

getCmdLine :: Idris [Opt]
getCmdLine = do i <- getIState
                return (opt_cmdline (idris_options i))

getDumpHighlighting :: Idris Bool
getDumpHighlighting = do ist <- getIState
                         return (findC (opt_cmdline (idris_options ist)))
  where findC = elem DumpHighlights

getDumpDefun :: Idris (Maybe FilePath)
getDumpDefun = do i <- getIState
                  return $ findC (opt_cmdline (idris_options i))
    where findC [] = Nothing
          findC (DumpDefun x : _) = Just x
          findC (_ : xs) = findC xs

getDumpCases :: Idris (Maybe FilePath)
getDumpCases = do i <- getIState
                  return $ findC (opt_cmdline (idris_options i))
    where findC [] = Nothing
          findC (DumpCases x : _) = Just x
          findC (_ : xs) = findC xs

logLevel :: Idris Int
logLevel = do i <- getIState
              return (opt_logLevel (idris_options i))

setAutoImpls :: Bool -> Idris ()
setAutoImpls b = do i <- getIState
                    let opts = idris_options i
                    let opt' = opts { opt_autoimpls = b }
                    putIState $ i { idris_options = opt' }

getAutoImpls :: Idris Bool
getAutoImpls = do i <- getIState
                  return (opt_autoimpls (idris_options i))

setErrContext :: Bool -> Idris ()
setErrContext t = do i <- getIState
                     let opts = idris_options i
                     let opts' = opts { opt_errContext = t }
                     putIState $ i { idris_options = opts' }

errContext :: Idris Bool
errContext = do i <- getIState
                return (opt_errContext (idris_options i))

getOptimise :: Idris [Optimisation]
getOptimise = do i <- getIState
                 return (opt_optimise (idris_options i))

setOptimise :: [Optimisation] -> Idris ()
setOptimise newopts = do i <- getIState
                         let opts = idris_options i
                         let opts' = opts { opt_optimise = newopts }
                         putIState $ i { idris_options = opts' }

addOptimise :: Optimisation -> Idris ()
addOptimise opt = do opts <- getOptimise
                     setOptimise (nub (opt : opts))

removeOptimise :: Optimisation -> Idris ()
removeOptimise opt = do opts <- getOptimise
                        setOptimise ((nub opts) \\ [opt])

-- | Set appropriate optimisation set for the given level. We only
-- have one optimisation that is configurable at the moment, however!
setOptLevel :: Int -> Idris ()
setOptLevel n | n <= 0 = setOptimise []
setOptLevel 1          = setOptimise []
setOptLevel 2          = setOptimise [PETransform]
setOptLevel n | n >= 3 = setOptimise [PETransform]

useREPL :: Idris Bool
useREPL = do i <- getIState
             return (opt_repl (idris_options i))

setREPL :: Bool -> Idris ()
setREPL t = do i <- getIState
               let opts = idris_options i
               let opt' = opts { opt_repl = t }
               putIState $ i { idris_options = opt' }

showOrigErr :: Idris Bool
showOrigErr = do i <- getIState
                 return (opt_origerr (idris_options i))

setShowOrigErr :: Bool -> Idris ()
setShowOrigErr b = do i <- getIState
                      let opts = idris_options i
                      let opt' = opts { opt_origerr = b }
                      putIState $ i { idris_options = opt' }

setAutoSolve :: Bool -> Idris ()
setAutoSolve b = do i <- getIState
                    let opts = idris_options i
                    let opt' = opts { opt_autoSolve = b }
                    putIState $ i { idris_options = opt' }

setNoBanner :: Bool -> Idris ()
setNoBanner n = do i <- getIState
                   let opts = idris_options i
                   let opt' = opts { opt_nobanner = n }
                   putIState $ i { idris_options = opt' }

getNoBanner :: Idris Bool
getNoBanner = do i <- getIState
                 let opts = idris_options i
                 return (opt_nobanner opts)

setEvalTypes :: Bool -> Idris ()
setEvalTypes n = do i <- getIState
                    let opts = idris_options i
                    let opt' = opts { opt_evaltypes = n }
                    putIState $ i { idris_options = opt' }

getDesugarNats :: Idris Bool
getDesugarNats = do i <- getIState
                    let opts = idris_options i
                    return (opt_desugarnats opts)


setDesugarNats :: Bool -> Idris ()
setDesugarNats n = do i <- getIState
                      let opts = idris_options i
                      let opt' = opts { opt_desugarnats = n }
                      putIState $ i { idris_options = opt' }

setQuiet :: Bool -> Idris ()
setQuiet q = do i <- getIState
                let opts = idris_options i
                let opt' = opts { opt_quiet = q }
                putIState $ i { idris_options = opt' }

getQuiet :: Idris Bool
getQuiet = do i <- getIState
              let opts = idris_options i
              return (opt_quiet opts)

setCodegen :: Codegen -> Idris ()
setCodegen t = do i <- getIState
                  let opts = idris_options i
                  let opt' = opts { opt_codegen = t }
                  putIState $ i { idris_options = opt' }

codegen :: Idris Codegen
codegen = do i <- getIState
             return (opt_codegen (idris_options i))


setOutputTy :: OutputType -> Idris ()
setOutputTy t = do i <- getIState
                   let opts = idris_options i
                   let opt' = opts { opt_outputTy = t }
                   putIState $ i { idris_options = opt' }

outputTy :: Idris OutputType
outputTy = do i <- getIState
              return $ opt_outputTy $ idris_options i

setIdeMode :: Bool -> Handle -> Idris ()
setIdeMode True  h = do i <- getIState
                        putIState $ i { idris_outputmode = IdeMode 0 h
                                      , idris_colourRepl = False
                                      }
setIdeMode False _ = return ()

setTargetTriple :: String -> Idris ()
setTargetTriple t = do i <- getIState
                       let opts = idris_options i
                           opt' = opts { opt_triple = t }
                       putIState $ i { idris_options = opt' }

targetTriple :: Idris String
targetTriple = do i <- getIState
                  return (opt_triple (idris_options i))

setTargetCPU :: String -> Idris ()
setTargetCPU t = do i <- getIState
                    let opts = idris_options i
                        opt' = opts { opt_cpu = t }
                    putIState $ i { idris_options = opt' }

targetCPU :: Idris String
targetCPU = do i <- getIState
               return (opt_cpu (idris_options i))

verbose :: Idris Int
verbose = do
  i <- getIState
  -- Quietness overrides verbosity
  let quiet = opt_quiet   $ idris_options i
  if quiet
    then return $ 0
    else return $ (opt_verbose $ idris_options i)

setVerbose :: Int -> Idris ()
setVerbose t = do
  i <- getIState
  let opts = idris_options i
  let opt' = opts { opt_verbose = t }
  putIState $ i { idris_options = opt' }

iReport :: Int -> String -> Idris ()
iReport level msg = do
  verbosity <- verbose
  i <- getIState
  when (level <= verbosity) $
    case idris_outputmode i of
      RawOutput h -> runIO $ hPutStrLn h msg
      IdeMode n h -> runIO . hPutStrLn h $ convSExp "write-string" msg n
  return ()

typeInType :: Idris Bool
typeInType = do i <- getIState
                return (opt_typeintype (idris_options i))

setTypeInType :: Bool -> Idris ()
setTypeInType t = do i <- getIState
                     let opts = idris_options i
                     let opt' = opts { opt_typeintype = t }
                     putIState $ i { idris_options = opt' }

coverage :: Idris Bool
coverage = do i <- getIState
              return (opt_coverage (idris_options i))

setCoverage :: Bool -> Idris ()
setCoverage t = do i <- getIState
                   let opts = idris_options i
                   let opt' = opts { opt_coverage = t }
                   putIState $ i { idris_options = opt' }

setIBCSubDir :: FilePath -> Idris ()
setIBCSubDir fp = do i <- getIState
                     let opts = idris_options i
                     let opt' = opts { opt_ibcsubdir = fp }
                     putIState $ i { idris_options = opt' }

valIBCSubDir :: IState -> Idris FilePath
valIBCSubDir i = return (opt_ibcsubdir (idris_options i))

addImportDir :: FilePath -> Idris ()
addImportDir fp = do i <- getIState
                     let opts = idris_options i
                     let opt' = opts { opt_importdirs = nub $ fp : opt_importdirs opts }
                     putIState $ i { idris_options = opt' }

setImportDirs :: [FilePath] -> Idris ()
setImportDirs fps = do i <- getIState
                       let opts = idris_options i
                       let opt' = opts { opt_importdirs = fps }
                       putIState $ i { idris_options = opt' }

allImportDirs :: Idris [FilePath]
allImportDirs = do i <- getIState
                   let optdirs = opt_importdirs (idris_options i)
                   return ("." : reverse optdirs)

addSourceDir :: FilePath -> Idris ()
addSourceDir fp = do i <- getIState
                     let opts = idris_options i
                     let opts' = opts { opt_sourcedirs = nub $ fp : opt_sourcedirs opts  }
                     putIState $ i { idris_options = opts' }

setSourceDirs :: [FilePath] -> Idris ()
setSourceDirs fps = do i <- getIState
                       let opts = idris_options i
                       let opts' = opts { opt_sourcedirs = nub $ fps  }
                       putIState $ i { idris_options = opts' }

allSourceDirs :: Idris [FilePath]
allSourceDirs = do i <- getIState
                   let optdirs = opt_sourcedirs (idris_options i)
                   return ("." : reverse optdirs)

colourise :: Idris Bool
colourise = do i <- getIState
               return $ idris_colourRepl i

setColourise :: Bool -> Idris ()
setColourise b = do i <- getIState
                    putIState $ i { idris_colourRepl = b }

impShow :: Idris Bool
impShow = do i <- getIState
             return (opt_showimp (idris_options i))

setImpShow :: Bool -> Idris ()
setImpShow t = do i <- getIState
                  let opts = idris_options i
                  let opt' = opts { opt_showimp = t }
                  putIState $ i { idris_options = opt' }

setColour :: ColourType -> IdrisColour -> Idris ()
setColour ct c = do i <- getIState
                    let newTheme = setColour' ct c (idris_colourTheme i)
                    putIState $ i { idris_colourTheme = newTheme }
    where setColour' KeywordColour   c t = t { keywordColour = c }
          setColour' BoundVarColour  c t = t { boundVarColour = c }
          setColour' ImplicitColour  c t = t { implicitColour = c }
          setColour' FunctionColour  c t = t { functionColour = c }
          setColour' TypeColour      c t = t { typeColour = c }
          setColour' DataColour      c t = t { dataColour = c }
          setColour' PromptColour    c t = t { promptColour = c }
          setColour' PostulateColour c t = t { postulateColour = c }

logLvl :: Int -> String -> Idris ()
logLvl = logLvlCats []

logCoverage :: Int -> String -> Idris ()
logCoverage = logLvlCats [ICoverage]

logErasure :: Int -> String -> Idris ()
logErasure = logLvlCats [IErasure]

-- | Log an action of the parser
logParser :: Int -> String -> Idris ()
logParser = logLvlCats parserCats

-- | Log an action of the elaborator.
logElab :: Int -> String -> Idris ()
logElab = logLvlCats elabCats

-- | Log an action of the compiler.
logCodeGen :: Int -> String -> Idris ()
logCodeGen = logLvlCats codegenCats

logIBC :: Int -> String -> Idris ()
logIBC = logLvlCats [IIBC]

-- | Log aspect of Idris execution
--
-- An empty set of logging levels is used to denote all categories.
--
-- @TODO update IDE protocol
logLvlCats :: [LogCat] -- ^ The categories that the message should appear under.
           -> Int      -- ^ The Logging level the message should appear.
           -> String   -- ^ The message to show the developer.
           -> Idris ()
logLvlCats cs l msg = do
    i <- getIState
    let lvl  = opt_logLevel (idris_options i)
    let cats = opt_logcats (idris_options i)
    when (lvl >= l) $
      when (inCat cs cats || null cats) $
        case idris_outputmode i of
          RawOutput h -> do
            runIO $ hPutStrLn h msg
          IdeMode n h -> do
            let good = SexpList [IntegerAtom (toInteger l), toSExp msg]
            runIO . hPutStrLn h $ convSExp "log" good n
  where
    inCat :: [LogCat] -> [LogCat] -> Bool
    inCat cs cats = any (`elem` cats) cs

cmdOptType :: Opt -> Idris Bool
cmdOptType x = do i <- getIState
                  return $ x `elem` opt_cmdline (idris_options i)

noErrors :: Idris Bool
noErrors = do i <- getIState
              case errSpan i of
                Nothing -> return True
                _       -> return False

setTypeCase :: Bool -> Idris ()
setTypeCase t = do i <- getIState
                   let opts = idris_options i
                   let opt' = opts { opt_typecase = t }
                   putIState $ i { idris_options = opt' }

getIndentWith :: Idris Int
getIndentWith = do
  i <- getIState
  return $ interactiveOpts_indentWith (idris_interactiveOpts i)

setIndentWith :: Int -> Idris ()
setIndentWith indentWith = do
  i <- getIState
  let opts = idris_interactiveOpts i
  let opts' = opts { interactiveOpts_indentWith = indentWith }
  putIState $ i { idris_interactiveOpts = opts' }

getIndentClause :: Idris Int
getIndentClause = do
  i <- getIState
  return $ interactiveOpts_indentClause (idris_interactiveOpts i)

setIndentClause :: Int -> Idris ()
setIndentClause indentClause = do
  i <- getIState
  let opts = idris_interactiveOpts i
  let opts' = opts { interactiveOpts_indentClause = indentClause }
  putIState $ i { idris_interactiveOpts = opts' }

-- Dealing with parameters

expandParams :: (Name -> Name) -> [(Name, PTerm)] ->
                [Name] -> -- all names
                [Name] -> -- names with no declaration
                PTerm -> PTerm
expandParams dec ps ns infs tm = en 0 tm
  where
    -- if we shadow a name (say in a lambda binding) that is used in a call to
    -- a lifted function, we need access to both names - once in the scope of the
    -- binding and once to call the lifted functions. So we'll explicitly shadow
    -- it. (Yes, it's a hack. The alternative would be to resolve names earlier
    -- but we didn't...)

    mkShadow (UN n) = MN 0 n
    mkShadow (MN i n) = MN (i+1) n
    mkShadow (NS x s) = NS (mkShadow x) s

    en :: Int -- ^ The quotation level - only transform terms that are used, not terms
              -- that are merely mentioned.
        -> PTerm -> PTerm
    en 0 (PLam fc n nfc t s)
       | n `elem` (map fst ps ++ ns)
               = let n' = mkShadow n in
                     PLam fc n' nfc (en 0 t) (en 0 (shadow n n' s))
       | otherwise = PLam fc n nfc (en 0 t) (en 0 s)
    en 0 (PPi p n nfc t s)
       | n `elem` (map fst ps ++ ns)
               = let n' = mkShadow n in -- TODO THINK SHADOWING TacImp?
                     PPi (enTacImp 0 p) n' nfc (en 0 t) (en 0 (shadow n n' s))
       | otherwise = PPi (enTacImp 0 p) n nfc (en 0 t) (en 0 s)
    en 0 (PLet fc n nfc ty v s)
       | n `elem` (map fst ps ++ ns)
               = let n' = mkShadow n in
                     PLet fc n' nfc (en 0 ty) (en 0 v) (en 0 (shadow n n' s))
       | otherwise = PLet fc n nfc (en 0 ty) (en 0 v) (en 0 s)
    -- FIXME: Should only do this in a type signature!
    en 0 (PDPair f hls p (PRef f' fcs n) t r)
       | n `elem` (map fst ps ++ ns) && t /= Placeholder
           = let n' = mkShadow n in
                 PDPair f hls p (PRef f' fcs n') (en 0 t) (en 0 (shadow n n' r))
    en 0 (PRewrite f by l r g) = PRewrite f by (en 0 l) (en 0 r) (fmap (en 0) g)
    en 0 (PTyped l r) = PTyped (en 0 l) (en 0 r)
    en 0 (PPair f hls p l r) = PPair f hls p (en 0 l) (en 0 r)
    en 0 (PDPair f hls p l t r) = PDPair f hls p (en 0 l) (en 0 t) (en 0 r)
    en 0 (PAlternative ns a as) = PAlternative ns a (map (en 0) as)
    en 0 (PHidden t) = PHidden (en 0 t)
    en 0 (PUnifyLog t) = PUnifyLog (en 0 t)
    en 0 (PDisamb ds t) = PDisamb ds (en 0 t)
    en 0 (PNoImplicits t) = PNoImplicits (en 0 t)
    en 0 (PDoBlock ds) = PDoBlock (map (fmap (en 0)) ds)
    en 0 (PProof ts)   = PProof (map (fmap (en 0)) ts)
    en 0 (PTactics ts) = PTactics (map (fmap (en 0)) ts)

    en 0 (PQuote (Var n))
        | n `nselem` ns = PQuote (Var (dec n))
    en 0 (PApp fc (PInferRef fc' hl n) as)
        | n `nselem` ns = PApp fc (PInferRef fc' hl (dec n))
                           (map ((pexp . (PRef fc hl)) . fst) ps ++ (map (fmap (en 0)) as))
    en 0 (PApp fc (PRef fc' hl n) as)
        | n `elem` infs = PApp fc (PInferRef fc' hl (dec n))
                           (map ((pexp . (PRef fc hl)) . fst) ps ++ (map (fmap (en 0)) as))
        | n `nselem` ns = PApp fc (PRef fc' hl (dec n))
                           (map ((pexp . (PRef fc hl)) . fst) ps ++ (map (fmap (en 0)) as))
    en 0 (PAppBind fc (PRef fc' hl n) as)
        | n `elem` infs = PAppBind fc (PInferRef fc' hl (dec n))
                           (map ((pexp . (PRef fc hl)) . fst) ps ++ (map (fmap (en 0)) as))
        | n `nselem` ns = PAppBind fc (PRef fc' hl (dec n))
                           (map ((pexp . (PRef fc hl)) . fst) ps ++ (map (fmap (en 0)) as))
    en 0 (PRef fc hl n)
        | n `elem` infs = PApp fc (PInferRef fc hl (dec n))
                           (map ((pexp . (PRef fc hl)) . fst) ps)
        | n `nselem` ns = PApp fc (PRef fc hl (dec n))
                           (map ((pexp . (PRef fc hl)) . fst) ps)
    en 0 (PInferRef fc hl n)
        | n `nselem` ns = PApp fc (PInferRef fc hl (dec n))
                           (map ((pexp . (PRef fc hl)) . fst) ps)
    en 0 (PApp fc f as) = PApp fc (en 0 f) (map (fmap (en 0)) as)
    en 0 (PAppBind fc f as) = PAppBind fc (en 0 f) (map (fmap (en 0)) as)
    en 0 (PCase fc c os) = PCase fc (en 0 c) (map (pmap (en 0)) os)
    en 0 (PIfThenElse fc c t f) = PIfThenElse fc (en 0 c) (en 0 t) (en 0 f)
    en 0 (PRunElab fc tm ns) = PRunElab fc (en 0 tm) ns
    en 0 (PConstSugar fc tm) = PConstSugar fc (en 0 tm)

    en ql (PQuasiquote tm ty) = PQuasiquote (en (ql + 1) tm) (fmap (en ql) ty)
    en ql (PUnquote tm) = PUnquote (en (ql - 1) tm)

    en ql t = descend (en ql) t

    nselem x [] = False
    nselem x (y : xs) | nseq x y = True
                      | otherwise = nselem x xs

    nseq x y = nsroot x == nsroot y

    enTacImp ql (TacImp aos st scr rig) = TacImp aos st (en ql scr) rig
    enTacImp ql other                   = other

expandParamsD :: Bool -> -- True = RHS only
                 IState ->
                 (Name -> Name) -> [(Name, PTerm)] -> [Name] -> PDecl -> PDecl
expandParamsD rhsonly ist dec ps ns (PTy doc argdocs syn fc o n nfc ty)
    = if n `elem` ns && (not rhsonly)
         then -- trace (show (n, expandParams dec ps ns ty)) $
              PTy doc argdocs syn fc o (dec n) nfc (piBindp expl_param ps (expandParams dec ps ns [] ty))
         else --trace (show (n, expandParams dec ps ns ty)) $
              PTy doc argdocs syn fc o n nfc (expandParams dec ps ns [] ty)
expandParamsD rhsonly ist dec ps ns (PPostulate e doc syn fc nfc o n ty)
    = if n `elem` ns && (not rhsonly)
         then -- trace (show (n, expandParams dec ps ns ty)) $
              PPostulate e doc syn fc nfc o (dec n)
                         (piBind ps (expandParams dec ps ns [] ty))
         else --trace (show (n, expandParams dec ps ns ty)) $
              PPostulate e doc syn fc nfc o n (expandParams dec ps ns [] ty)
expandParamsD rhsonly ist dec ps ns (PClauses fc opts n cs)
    = let n' = if n `elem` ns then dec n else n in
          PClauses fc opts n' (map expandParamsC cs)
  where
    expandParamsC (PClause fc n lhs ws rhs ds)
        = let -- ps' = updateps True (namesIn ist rhs) (zip ps [0..])
              ps'' = updateps False (namesIn [] ist lhs) (zip ps [0..])
              lhs' = if rhsonly then lhs else (expandParams dec ps'' ns [] lhs)
              n' = if n `elem` ns then dec n else n
              -- names bound on the lhs should not be expanded on the rhs
              ns' = removeBound lhs ns in
              PClause fc n' lhs'
                            (map (expandParams dec ps'' ns' []) ws)
                            (expandParams dec ps'' ns' [] rhs)
                            (map (expandParamsD True ist dec ps'' ns') ds)
    expandParamsC (PWith fc n lhs ws wval pn ds)
        = let -- ps' = updateps True (namesIn ist wval) (zip ps [0..])
              ps'' = updateps False (namesIn [] ist lhs) (zip ps [0..])
              lhs' = if rhsonly then lhs else (expandParams dec ps'' ns [] lhs)
              n' = if n `elem` ns then dec n else n
              ns' = removeBound lhs ns in
              PWith fc n' lhs'
                          (map (expandParams dec ps'' ns' []) ws)
                          (expandParams dec ps'' ns' [] wval)
                          pn
                          (map (expandParamsD rhsonly ist dec ps'' ns') ds)
    updateps yn nm [] = []
    updateps yn nm (((a, t), i):as)
        | (a `elem` nm) == yn = (a, t) : updateps yn nm as
        | otherwise = (sMN i (show a ++ "_shadow"), t) : updateps yn nm as

    removeBound lhs ns = ns \\ nub (bnames lhs)

    bnames (PRef _ _ n) = [n]
    bnames (PApp _ _ args) = concatMap (bnames . getTm) args
    bnames (PPair _ _ _ l r) = bnames l ++ bnames r
    bnames (PDPair _ _ _ l Placeholder r) = bnames l ++ bnames r
    bnames _ = []

-- | Expands parameters defined in parameter and where blocks inside of declarations
expandParamsD rhs ist dec ps ns (PData doc argDocs syn fc co pd)
    = PData doc argDocs syn fc co (expandPData pd)
  where
    -- just do the type decl, leave constructors alone (parameters will be
    -- added implicitly)
    expandPData (PDatadecl n nfc ty cons)
       = if n `elem` ns
            then PDatadecl (dec n) nfc (piBind ps (expandParams dec ps ns [] ty))
                           (map econ cons)
            else PDatadecl n nfc (expandParams dec ps ns [] ty) (map econ cons)
    econ (doc, argDocs, n, nfc, t, fc, fs)
       = (doc, argDocs, dec n, nfc, piBindp expl ps (expandParams dec ps ns [] t), fc, fs)
expandParamsD rhs ist dec ps ns d@(PRecord doc rsyn fc opts name nfc prs pdocs fls cn cdoc csyn)
  = d
expandParamsD rhs ist dec ps ns (PParams f params pds)
   = PParams f (ps ++ map (mapsnd (expandParams dec ps ns [])) params)
               (map (expandParamsD True ist dec ps ns) pds)
--                (map (expandParamsD ist dec ps ns) pds)
expandParamsD rhs ist dec ps ns (PMutual f pds)
   = PMutual f (map (expandParamsD rhs ist dec ps ns) pds)
expandParamsD rhs ist dec ps ns (PInterface doc info f cs n nfc params pDocs fds decls cn cd)
   = PInterface doc info f
           (map (\ (n, t) -> (n, expandParams dec ps ns [] t)) cs)
           n nfc
           (map (\(n, fc, t) -> (n, fc, expandParams dec ps ns [] t)) params)
           pDocs
           fds
           (map (expandParamsD rhs ist dec ps ns) decls)
           cn
           cd
expandParamsD rhs ist dec ps ns (PImplementation doc argDocs info f cs pnames acc opts n nfc params pextra ty cn decls)
   = let cn' = case cn of
                    Just n -> if n `elem` ns then Just (dec n) else Just n
                    Nothing -> Nothing in
     PImplementation doc argDocs info f
                     (map (\ (n, t) -> (n, expandParams dec ps ns [] t)) cs)
                     pnames acc opts n
                     nfc
                     (map (expandParams dec ps ns []) params)
                     (map (\ (n, t) -> (n, expandParams dec ps ns [] t)) pextra)
                     (expandParams dec ps ns [] ty)
                     cn'
                     (map (expandParamsD True ist dec ps ns) decls)
expandParamsD rhs ist dec ps ns d = d

mapsnd f (x, t) = (x, f t)

expandImplementationScope ist dec ps ns (PImplementation doc argDocs info f cs pnames acc opts n nfc params pextra ty cn decls)
    = PImplementation doc argDocs info f cs pnames acc opts n nfc params (ps ++ pextra)
                      ty cn decls
expandImplementationScope ist dec ps ns d = d

-- | Calculate a priority for a type, for deciding elaboration order
-- * if it's just a type variable or concrete type, do it early (0)
-- * if there's only type variables and injective constructors, do it next (1)
-- * if there's a function type, next (2)
-- * finally, everything else (3)
getPriority :: IState -> PTerm -> Int
getPriority i tm = 1 -- pri tm
  where
    pri (PRef _ _ n) =
        case lookupP n (tt_ctxt i) of
            ((P (DCon _ _ _) _ _):_) -> 1
            ((P (TCon _ _) _ _):_) -> 1
            ((P Ref _ _):_) -> 1
            [] -> 0 -- must be locally bound, if it's not an error...
    pri (PPi _ _ _ x y) = max 5 (max (pri x) (pri y))
    pri (PTrue _ _) = 0
    pri (PRewrite _ _ l r _) = max 1 (max (pri l) (pri r))
    pri (PApp _ f as) = max 1 (max (pri f) (foldr (max . pri . getTm) 0 as))
    pri (PAppBind _ f as) = max 1 (max (pri f) (foldr (max . pri . getTm) 0 as))
    pri (PCase _ f as) = max 1 (max (pri f) (foldr (max . pri . snd) 0 as))
    pri (PTyped l r) = pri l
    pri (PPair _ _ _ l r) = max 1 (max (pri l) (pri r))
    pri (PDPair _ _ _ l t r) = max 1 (max (pri l) (max (pri t) (pri r)))
    pri (PAlternative _ a as) = maximum (map pri as)
    pri (PConstant _ _) = 0
    pri Placeholder = 1
    pri _ = 3


addStatics :: Name -> Term -> PTerm -> Idris ()
addStatics n tm ptm =
    do let (statics, dynamics) = initStatics tm ptm
       ist <- getIState
       let paramnames
              = nub $ case lookupCtxtExact n (idris_fninfo ist) of
                           Just p -> getNamesFrom 0 (fn_params p) tm ++
                                     concatMap (getParamNames ist . snd) statics
                           _ -> concatMap (getParamNames ist . snd) statics

       let stnames = nub $ concatMap (freeArgNames . snd) statics
       let dnames = (nub $ concatMap (freeArgNames . snd) dynamics)
                             \\ paramnames
       -- also get the arguments which are 'uniquely inferrable' from
       -- statics (see sec 4.2 of "Scrapping Your Inefficient Engine")
       -- or parameters to the type of a static
       let statics' = nub $ map fst statics ++
                              filter (\x -> not (elem x dnames)) stnames
       let stpos = staticList statics' tm
       i <- getIState
       unless (null statics) $
          logLvl 3 $ "Statics for " ++ show n ++ " " ++ show tm ++ "\n"
                        ++ showTmImpls ptm ++ "\n"
                        ++ show statics ++ "\n" ++ show dynamics
                        ++ "\n" ++ show paramnames
                        ++ "\n" ++ show stpos
       putIState $ i { idris_statics = addDef n stpos (idris_statics i) }
       addIBC (IBCStatic n)
  where
    initStatics (Bind n (Pi _ _ ty _) sc) (PPi p n' fc t s)
            | n /= n' = let (static, dynamic) = initStatics sc (PPi p n' fc t s) in
                            (static, (n, ty) : dynamic)
    initStatics (Bind n (Pi _ _ ty _) sc) (PPi p n' fc _ s)
            = let (static, dynamic) = initStatics (instantiate (P Bound n ty) sc) s in
                  if pstatic p == Static then ((n, ty) : static, dynamic)
                    else if (not (searchArg p))
                            then (static, (n, ty) : dynamic)
                            else (static, dynamic)
    initStatics t pt = ([], [])

    getParamNames ist tm | (P _ n _ , args) <- unApply tm
       = case lookupCtxtExact n (idris_datatypes ist) of
              Just ti -> getNamePos 0 (param_pos ti) args
              Nothing -> []
      where getNamePos i ps [] = []
            getNamePos i ps (P _ n _ : as)
                 | i `elem` ps = n : getNamePos (i + 1) ps as
            getNamePos i ps (_ : as) = getNamePos (i + 1) ps as
    getParamNames ist (Bind t (Pi _ _ (P _ n _) _) sc)
       = n : getParamNames ist sc
    getParamNames ist _ = []

    getNamesFrom i ps (Bind n (Pi _ _ _ _) sc)
       | i `elem` ps = n : getNamesFrom (i + 1) ps sc
       | otherwise = getNamesFrom (i + 1) ps sc
    getNamesFrom i ps sc = []

    freeArgNames (Bind n (Pi _ _ ty _) sc)
          = nub $ freeNames ty ++ freeNames sc -- treat '->' as fn here
    freeArgNames tm = let (_, args) = unApply tm in
                          concatMap freeNames args

    -- if a name appears in an interface or tactic implicit index, it doesn't
    -- affect its 'uniquely inferrable' from a static status since these are
    -- resolved by searching.
    searchArg (Constraint _ _ _) = True
    searchArg (TacImp _ _ _ _) = True
    searchArg _ = False

    staticList sts (Bind n (Pi _ _ _ _) sc) = (n `elem` sts) : staticList sts sc
    staticList _ _ = []

-- Dealing with implicit arguments

-- Add some bound implicits to the using block if they aren't there already

addToUsing :: [Using] -> [(Name, PTerm)] -> [Using]
addToUsing us [] = us
addToUsing us ((n, t) : ns)
   | n `notElem` mapMaybe impName us = addToUsing (us ++ [UImplicit n t]) ns
   | otherwise = addToUsing us ns
  where impName (UImplicit n _) = Just n
        impName _ = Nothing

-- Add constraint bindings from using block

addUsingConstraints :: SyntaxInfo -> FC -> PTerm -> Idris PTerm
addUsingConstraints syn fc t
   = do ist <- get
        let ns = namesIn [] ist t
        let cs = getConstraints t -- check declared constraints
        let addconsts = uconsts \\ cs
        return (doAdd addconsts ns t)
   where uconsts = filter uconst (using syn)
         uconst (UConstraint _ _) = True
         uconst _ = False

         doAdd [] _ t = t
         -- if all of args in ns, then add it
         doAdd (UConstraint c args : cs) ns t
             | all (\n -> elem n ns) args
                   = PPi (Constraint [] Dynamic RigW) (sMN 0 "cu") NoFC
                         (mkConst c args) (doAdd cs ns t)
             | otherwise = doAdd cs ns t

         mkConst c args = PApp fc (PRef fc [] c)
                           (map (PExp 0 [] (sMN 0 "carg") . PRef fc []) args)

         getConstraints (PPi (Constraint _ _ _) _ _ c sc)
             = getcapp c ++ getConstraints sc
         getConstraints (PPi _ _ _ c sc) = getConstraints sc
         getConstraints _ = []

         getcapp (PApp _ (PRef _ _ c) args)
             = do ns <- mapM getName args
                  return (UConstraint c ns)
         getcapp _ = []

         getName (PExp _ _ _ (PRef _ _ n)) = return n
         getName _ = []

-- | Add implicit bindings from using block, and bind any missing names
addUsingImpls :: SyntaxInfo -> Name -> FC -> PTerm -> Idris PTerm
addUsingImpls syn n fc t
   = do ist <- getIState
        autoimpl <- getAutoImpls
        let ns_in = implicitNamesIn (map iname uimpls) ist t
        let ns = if autoimpl then ns_in
                    else filter (\n -> n `elem` (map iname uimpls)) ns_in

        let badnames = filter (\n -> not (implicitable n) &&
                                     n `notElem` (map iname uimpls)) ns
        unless (null badnames) $
           throwError (At fc (Elaborating "type of " n Nothing
                         (NoSuchVariable (head badnames))))
        let cs = getArgnames t -- get already bound names
        let addimpls = filter (\n -> iname n `notElem` cs) uimpls
        -- if all names in the arguments of addconsts appear in ns,
        -- add the constraint implicitly
        return (bindFree ns (doAdd addimpls ns t))
   where uimpls = filter uimpl (using syn)
         uimpl (UImplicit _ _) = True
         uimpl _ = False

         iname (UImplicit n _) = n
         iname (UConstraint _ _) = error "Can't happen addUsingImpls"

         doAdd [] _ t = t
         -- if all of args in ns, then add it
         doAdd (UImplicit n ty : cs) ns t
             | elem n ns
                   = PPi impl_gen n NoFC ty (doAdd cs ns t)
             | otherwise = doAdd cs ns t

         -- bind the free names which weren't in the using block
         bindFree [] tm = tm
         bindFree (n:ns) tm
             | elem n (map iname uimpls) = bindFree ns tm
             | otherwise
                    = PPi (impl_gen { pargopts = [InaccessibleArg] }) n NoFC Placeholder (bindFree ns tm)

         getArgnames (PPi _ n _ c sc)
             = n : getArgnames sc
         getArgnames _ = []

-- Given the original type and the elaborated type, return the implicitness
-- status of each pi-bound argument, and whether it's inaccessible (True) or not.

getUnboundImplicits :: IState -> Type -> PTerm -> [(Bool, PArg)]
getUnboundImplicits i t tm = getImps t (collectImps tm)
  where collectImps (PPi p n _ t sc)
            = (n, (p, t)) : collectImps sc
        collectImps _ = []

        scopedimpl (Just i) = not (toplevel_imp i)
        scopedimpl _ = False

        getImps (Bind n (Pi _ i _ _) sc) imps
             | scopedimpl i = getImps sc imps
        getImps (Bind n (Pi _ _ t _) sc) imps
            | Just (p, t') <- lookup n imps = argInfo n p t' : getImps sc imps
         where
            argInfo n (Imp opt _ _ _ _ _) Placeholder
                   = (True, PImp 0 True opt n Placeholder)
            argInfo n (Imp opt _ _ _ _ _) t'
                   = (False, PImp (getPriority i t') True opt n t')
            argInfo n (Exp opt _ _ _) t'
                   = (InaccessibleArg `elem` opt,
                          PExp (getPriority i t') opt n t')
            argInfo n (Constraint opt _ _) t'
                   = (InaccessibleArg `elem` opt,
                          PConstraint 10 opt n t')
            argInfo n (TacImp opt _ scr _) t'
                   = (InaccessibleArg `elem` opt,
                          PTacImplicit 10 opt n scr t')
        getImps (Bind n (Pi _ _ t _) sc) imps = impBind n t : getImps sc imps
           where impBind n t = (True, PImp 1 True [] n Placeholder)
        getImps sc tm = []

-- Add implicit Pi bindings for any names in the term which appear in an
-- argument position.

-- This has become a right mess already. Better redo it some time...
-- TODO: This is obsoleted by the new way of elaborating types, (which
-- calls addUsingImpls) but there's still a couple of places which use
-- it. Clean them up!
--
-- Issue 1739 in the issue tracker
--     https://github.com/idris-lang/Idris-dev/issues/1739
implicit :: ElabInfo -> SyntaxInfo -> Name -> PTerm -> Idris PTerm
implicit info syn n ptm = implicit' info syn [] n ptm

implicit' :: ElabInfo -> SyntaxInfo -> [Name] -> Name -> PTerm -> Idris PTerm
implicit' info syn ignore n ptm
    = do i <- getIState
         auto <- getAutoImpls
         let (tm', impdata) = implicitise auto syn ignore i ptm
         defaultArgCheck (eInfoNames info ++ M.keys (idris_implicits i)) impdata
--          let (tm'', spos) = findStatics i tm'
         putIState $ i { idris_implicits = addDef n impdata (idris_implicits i) }
         addIBC (IBCImp n)
         logLvl 5 ("Implicit " ++ show n ++ " " ++ show impdata)
--          i <- get
--          putIState $ i { idris_statics = addDef n spos (idris_statics i) }
         return tm'
  where
    --  Detect unknown names in default arguments and throw error if found.
    defaultArgCheck :: [Name] -> [PArg] -> Idris ()
    defaultArgCheck knowns params = foldM_ notFoundInDefault knowns params

    notFoundInDefault :: [Name] -> PArg -> Idris [Name]
    notFoundInDefault kns (PTacImplicit _ _ n script _)
      = do  i <- getIState
            case notFound kns (namesIn [] i script) of
              Nothing     -> return (n:kns)
              Just name   -> throwError (NoSuchVariable name)
    notFoundInDefault kns p = return ((pname p):kns)

    notFound :: [Name] -> [Name] -> Maybe Name
    notFound kns [] = Nothing
    notFound kns (SN (WhereN _ _ _) : ns) = notFound kns ns --  Known already
    notFound kns (n:ns) = if elem n kns then notFound kns ns else Just n

-- | Even if auto_implicits is off, we need to call this so we record
-- which arguments are implicit
implicitise :: Bool -> SyntaxInfo -> [Name] -> IState -> PTerm -> (PTerm, [PArg])
implicitise auto syn ignore ist tm = -- trace ("INCOMING " ++ showImp True tm) $
      let (declimps, ns') = execState (imps True [] tm) ([], [])
          ns = filter (\n -> auto && implicitable n || elem n (map fst uvars)) $
                  ns' \\ (map fst pvars ++ no_imp syn ++ ignore)
          nsOrder = filter (not . inUsing) ns ++ filter inUsing ns in
          if null ns
            then (tm, reverse declimps)
            else implicitise auto syn ignore ist (pibind uvars nsOrder tm)
  where
    uvars = map ipair (filter uimplicit (using syn))
    pvars = syn_params syn

    inUsing n = n `elem` map fst uvars

    ipair (UImplicit x y) = (x, y)
    uimplicit (UImplicit _ _) = True
    uimplicit _ = False

    dropAll (x:xs) ys | x `elem` ys = dropAll xs ys
                      | otherwise   = x : dropAll xs ys
    dropAll [] ys = []

    -- Find names in argument position in a type, suitable for implicit
    -- binding
    -- Not the function position, but do everything else...
    implNamesIn uv (PApp fc f args) = concatMap (implNamesIn uv . getTm) args
    implNamesIn uv t = implicitNamesIn (map fst uv) ist t

    imps top env ty@(PApp _ f as)
       = do (decls, ns) <- get
            let isn = nub (implNamesIn uvars ty)
            put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PPi (Imp l _ _ _ _ _) n _ ty sc)
        = do let isn = nub (implNamesIn uvars ty) `dropAll` [n]
             (decls , ns) <- get
             put (PImp (getPriority ist ty) True l n Placeholder : decls,
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (Exp l _ _ _) n _ ty sc)
        = do let isn = nub (implNamesIn uvars ty ++ case sc of
                            (PRef _ _ x) -> namesIn uvars ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PExp (getPriority ist ty) l n Placeholder : decls,
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (Constraint l _ _) n _ ty sc)
        = do let isn = nub (implNamesIn uvars ty ++ case sc of
                            (PRef _ _ x) -> namesIn uvars ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PConstraint 10 l n Placeholder : decls,
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (TacImp l _ scr _) n _ ty sc)
        = do let isn = nub (implNamesIn uvars ty ++ case sc of
                            (PRef _ _ x) -> namesIn uvars ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PTacImplicit 10 l n scr Placeholder : decls,
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PRewrite _ _ l r _)
        = do (decls, ns) <- get
             let isn = namesIn uvars ist l ++ namesIn uvars ist r
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PTyped l r)
        = imps top env l
    imps top env (PPair _ _ _ l r)
        = do (decls, ns) <- get
             let isn = namesIn uvars ist l ++ namesIn uvars ist r
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PDPair _ _ _ (PRef _ _ n) t r)
        = do (decls, ns) <- get
             let isn = nub (namesIn uvars ist t ++ namesIn uvars ist r) \\ [n]
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PDPair _ _ _ l t r)
        = do (decls, ns) <- get
             let isn = namesIn uvars ist l ++ namesIn uvars ist t ++
                       namesIn uvars ist r
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PAlternative ms a as)
        = do (decls, ns) <- get
             let isn = concatMap (namesIn uvars ist) as
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PLam fc n _ ty sc)
        = do imps False env ty
             imps False (n:env) sc
    imps top env (PHidden tm)    = imps False env tm
    imps top env (PUnifyLog tm)  = imps False env tm
    imps top env (PNoImplicits tm)  = imps False env tm
    imps top env (PRunElab fc tm ns) = imps False env tm
    imps top env (PConstSugar fc tm) = imps top env tm -- ignore PConstSugar - it's for highlighting only!
    imps top env _               = return ()

    pibind using []     sc = sc
    pibind using (n:ns) sc
      = case lookup n using of
            Just ty -> PPi impl_gen
                           n NoFC ty (pibind using ns sc)
            Nothing -> PPi (impl_gen { pargopts = [InaccessibleArg] })
                           n NoFC Placeholder (pibind using ns sc)

-- | Add implicit arguments in function calls
addImplPat :: IState -> PTerm -> PTerm
addImplPat = addImpl' True [] [] []

addImplBound :: IState -> [Name] -> PTerm -> PTerm
addImplBound ist ns = addImpl' False ns [] [] ist

addImplBoundInf :: IState -> [Name] -> [Name] -> PTerm -> PTerm
addImplBoundInf ist ns inf = addImpl' False ns inf [] ist

-- | Add the implicit arguments to applications in the term [Name]
-- gives the names to always expend, even when under a binder of that
-- name (this is to expand methods with implicit arguments in
-- dependent interfaces).
addImpl :: [Name] -> IState -> PTerm -> PTerm
addImpl = addImpl' False [] []

-- TODO: in patterns, don't add implicits to function names guarded by constructors
-- and *not* inside a PHidden

addImpl' :: Bool -> [Name] -> [Name] -> [Name] -> IState -> PTerm -> PTerm
addImpl' inpat env infns imp_meths ist ptm
   = ai inpat False (zip env (repeat Nothing)) [] (mkUniqueNames env [] ptm)
  where
    topname = case ptm of
                   PRef _ _ n -> n
                   PApp _ (PRef _ _ n) _ -> n
                   _ -> sUN "" -- doesn't matter then

    ai :: Bool -> Bool -> [(Name, Maybe PTerm)] -> [[T.Text]] -> PTerm -> PTerm
    ai inpat qq env ds (PRef fc fcs f)
        | f `elem` infns = PInferRef fc fcs f
        | not (f `elem` map fst env) = handleErr $ aiFn topname inpat inpat qq imp_meths ist fc f fc ds []
    ai inpat qq env ds (PHidden (PRef fc hl f))
        | not (f `elem` map fst env) = PHidden (handleErr $ aiFn topname inpat False qq imp_meths ist fc f fc ds [])
    ai inpat qq env ds (PRewrite fc by l r g)
       = let l' = ai inpat qq env ds l
             r' = ai inpat qq env ds r
             g' = fmap (ai inpat qq env ds) g in
         PRewrite fc by l' r' g'
    ai inpat qq env ds (PTyped l r)
      = let l' = ai inpat qq env ds l
            r' = ai inpat qq env ds r in
            PTyped l' r'
    ai inpat qq env ds (PPair fc hls p l r)
      = let l' = ai inpat qq env ds l
            r' = ai inpat qq env ds r in
            PPair fc hls p l' r'
    ai inpat qq env ds (PDPair fc hls p l t r)
         = let l' = ai inpat qq env ds l
               t' = ai inpat qq env ds t
               r' = ai inpat qq env ds r in
           PDPair fc hls p l' t' r'
    ai inpat qq env ds (PAlternative ms a as)
           = let as' = map (ai inpat qq env ds) as in
                 PAlternative ms a as'
    ai inpat qq env _ (PDisamb ds' as) = ai inpat qq env ds' as
    ai inpat qq env ds (PApp fc (PInferRef ffc hl f) as)
        = let as' = map (fmap (ai inpat qq env ds)) as in
              PApp fc (PInferRef ffc hl f) as'
    ai inpat qq env ds (PApp fc ftm@(PRef ffc hl f) as)
        | f `elem` infns = ai inpat qq env ds (PApp fc (PInferRef ffc hl f) as)
        | not (f `elem` map fst env)
              = let as' = map (fmap (ai inpat qq env ds)) as in
                    handleErr $ aiFn topname inpat False qq imp_meths ist fc f ffc ds as'
        | Just (Just ty) <- lookup f env =
             let as' = map (fmap (ai inpat qq env ds)) as
                 arity = getPArity ty in
              mkPApp fc arity ftm as'
    ai inpat qq env ds (PApp fc f as)
      = let f' = ai inpat qq env ds f
            as' = map (fmap (ai inpat qq env ds)) as in
            mkPApp fc 1 f' as'
    ai inpat qq env ds (PWithApp fc f a)
      = PWithApp fc (ai inpat qq env ds f) (ai inpat qq env ds a)
    ai inpat qq env ds (PCase fc c os)
      = let c' = ai inpat qq env ds c in
        -- leave lhs alone, because they get lifted into a new pattern match
        -- definition which is passed through addImpl again
            PCase fc c' (map aiCase os)
     where
       aiCase (lhs, rhs)
            = (lhs, ai inpat qq (env ++ patnames lhs) ds rhs)

       -- Anything beginning with a lower case letter, not applied,
       -- and no namespace is a pattern variable
       patnames (PApp _ (PRef _ _ f) [])
           | implicitable f = [(f, Nothing)]
       patnames (PRef _ _ f)
           | implicitable f = [(f, Nothing)]
       patnames (PApp _ (PRef _ _ _) args)
           = concatMap patnames (map getTm args)
       patnames (PPair _ _ _ l r) = patnames l ++ patnames r
       patnames (PDPair _ _ _ l t r) = patnames l ++ patnames t ++ patnames r
       patnames (PAs _ _ t) = patnames t
       patnames (PAlternative _ _ ts) = concatMap patnames ts
       patnames _ = []


    ai inpat qq env ds (PIfThenElse fc c t f) = PIfThenElse fc (ai inpat qq env ds c)
                                                         (ai inpat qq env ds t)
                                                         (ai inpat qq env ds f)

    -- If the name in a lambda is an unapplied data constructor name, do this
    -- as a 'case' instead because we'll expect to match on it
    ai inpat qq env ds (PLam fc n nfc ty sc)
      = if canBeDConName n (tt_ctxt ist)
             then ai inpat qq env ds (PLam fc (sMN 0 "lamp") NoFC ty
                                     (PCase fc (PRef fc [] (sMN 0 "lamp") )
                                        [(PRef fc [] n, sc)]))
             else let ty' = ai inpat qq env ds ty
                      sc' = ai inpat qq ((n, Just ty):env) ds sc in
                      PLam fc n nfc ty' sc'
    ai inpat qq env ds (PLet fc n nfc ty val sc)
      = if canBeDConName n (tt_ctxt ist)
           then ai inpat qq env ds (PCase fc val [(PRef fc [] n, sc)])
           else let ty' = ai inpat qq env ds ty
                    val' = ai inpat qq env ds val
                    sc' = ai inpat qq ((n, Just ty):env) ds sc in
                    PLet fc n nfc ty' val' sc'
    ai inpat qq env ds (PPi p n nfc ty sc)
      = let ty' = ai inpat qq env ds ty
            env' = if n `elem` imp_meths then env
                      else
                      ((n, Just ty) : env)
            sc' = ai inpat qq env' ds sc in
            PPi p n nfc ty' sc'
    ai inpat qq env ds (PGoal fc r n sc)
      = let r' = ai inpat qq env ds r
            sc' = ai inpat qq ((n, Nothing):env) ds sc in
            PGoal fc r' n sc'
    ai inpat qq env ds (PHidden tm) = PHidden (ai inpat qq env ds tm)
    -- Don't do PProof or PTactics since implicits get added when scope is
    -- properly known in ElabTerm.runTac
    ai inpat qq env ds (PUnifyLog tm) = PUnifyLog (ai inpat qq env ds tm)
    ai inpat qq env ds (PNoImplicits tm) = PNoImplicits (ai inpat qq env ds tm)
    ai inpat qq env ds (PQuasiquote tm g) = PQuasiquote (ai inpat True env ds tm)
                                                  (fmap (ai inpat True env ds) g)
    ai inpat qq env ds (PUnquote tm) = PUnquote (ai inpat False env ds tm)
    ai inpat qq env ds (PRunElab fc tm ns) = PRunElab fc (ai inpat False env ds tm) ns
    ai inpat qq env ds (PConstSugar fc tm) = PConstSugar fc (ai inpat qq env ds tm)
    ai inpat qq env ds tm = tm

    handleErr (Left err) = PElabError err
    handleErr (Right x) = x

-- if in a pattern, and there are no arguments, and there's no possible
-- names with zero explicit arguments, don't add implicits.

aiFn :: Name -> Bool -> Bool -> Bool
     -> [Name]
     -> IState -> FC
     -> Name -- ^ function being applied
     -> FC -> [[T.Text]]
     -> [PArg] -- ^ initial arguments (if in a pattern)
     -> Either Err PTerm
aiFn topname inpat True qq imp_meths ist fc f ffc ds []
  | inpat && implicitable f && unqualified f = Right $ PPatvar ffc f
  | otherwise
     = case lookupDef f (tt_ctxt ist) of
        [] -> Right $ PPatvar ffc f
        alts -> let ialts = lookupCtxtName f (idris_implicits ist) in
                    -- trace (show f ++ " " ++ show (fc, any (all imp) ialts, ialts, any constructor alts)) $
                    if (not (vname f) || tcname f
                           || any (conCaf (tt_ctxt ist)) ialts)
--                            any constructor alts || any allImp ialts))
                        then aiFn topname inpat False qq imp_meths ist fc f ffc ds [] -- use it as a constructor
                        else Right $ PPatvar ffc f
    where imp (PExp _ _ _ _) = False
          imp _ = True
--           allImp [] = False
          allImp xs = all imp xs

          unqualified (NS _ _) = False
          unqualified _ = True

          constructor (TyDecl (DCon _ _ _) _) = True
          constructor _ = False

          conCaf ctxt (n, cia) = (isDConName n ctxt || (qq && isTConName n ctxt)) && allImp cia

          vname (UN n) = True -- non qualified
          vname _ = False

aiFn topname inpat expat qq imp_meths ist fc f ffc ds as
    | f `elem` primNames = Right $ PApp fc (PRef ffc [ffc] f) as
aiFn topname inpat expat qq imp_meths ist fc f ffc ds as
          -- This is where namespaces get resolved by adding PAlternative
     = do let ns = lookupCtxtName f (idris_implicits ist)
          let nh = filter (\(n, _) -> notHidden n) ns
          let ns' = case trimAlts ds nh of
                         [] -> nh
                         x -> x
          case ns' of
            [(f',ns)] -> Right $ mkPApp fc (length ns) (PRef ffc [ffc] (isImpName f f'))
                                     (insertImpl ns as)
            [] -> case metaVar f (map fst (idris_metavars ist)) of
                    Just f' -> Right $ PApp fc (PRef ffc [ffc] f') as
                    Nothing -> Right $ mkPApp fc (length as) (PRef ffc [ffc] f) as
            alts -> Right $
                         PAlternative [] (ExactlyOne True) $
                           map (\(f', ns) -> mkPApp fc (length ns) (PRef ffc [ffc] (isImpName f f'))
                                                  (insertImpl ns as)) alts
  where
    -- if the name is in imp_meths, we should actually refer to the bound
    -- name rather than the global one after expanding implicits
    isImpName f f' | f `elem` imp_meths = f
                   | otherwise = f'

    -- If it's a metavariable name, try to qualify it from the list of
    -- unsolved metavariables
    metaVar f (mvn : ns) | f == nsroot mvn = Just mvn
    metaVar f (_ : ns) = metaVar f ns
    metaVar f [] = Nothing

    trimAlts [] alts = alts
    trimAlts ns alts
        = filter (\(x, _) -> any (\d -> d `isPrefixOf` nspace x) ns) alts

    nspace (NS _ s) = s
    nspace _ = []

    notHidden n = case getAccessibility n of
                        Hidden -> False
                        Private -> False
                        _ -> True

    getAccessibility n
             = case lookupDefAccExact n False (tt_ctxt ist) of
                    Just (n,t) -> t
                    _ -> Public

    insertImpl :: [PArg] -- ^ expected argument types (from idris_implicits)
               -> [PArg] -- ^ given arguments
               -> [PArg]
    insertImpl ps as
        = let (as', badimpls) = partition (impIn ps) as in
              map addUnknownImp badimpls ++
              insImpAcc M.empty ps (filter expArg as') (filter (not . expArg) as')

    insImpAcc :: M.Map Name PTerm -- accumulated param names & arg terms
              -> [PArg]           -- parameters
              -> [PArg]           -- explicit arguments
              -> [PArg]           -- implicits given
              -> [PArg]
    insImpAcc pnas (PExp p l n ty : ps) (PExp _ _ _ tm : given) imps =
      PExp p l n tm : insImpAcc (M.insert n tm pnas) ps given imps
    insImpAcc pnas (PConstraint p l n ty : ps) (PConstraint _ _ _ tm : given) imps =
      PConstraint p l n tm : insImpAcc (M.insert n tm pnas) ps given imps
    insImpAcc pnas (PConstraint p l n ty : ps) given imps =
      let rtc = PResolveTC fc in
        PConstraint p l n rtc : insImpAcc (M.insert n rtc pnas) ps given imps
    insImpAcc pnas (PImp p _ l n ty : ps) given imps =
        case find n imps [] of
            Just (tm, imps') ->
              PImp p False l n tm : insImpAcc (M.insert n tm pnas) ps given imps'
            Nothing ->
              PImp p True l n Placeholder :
                insImpAcc (M.insert n Placeholder pnas) ps given imps
    insImpAcc pnas (PTacImplicit p l n sc' ty : ps) given imps =
      let sc = addImpl imp_meths ist (substMatches (M.toList pnas) sc') in
        case find n imps [] of
            Just (tm, imps') ->
              PTacImplicit p l n sc tm :
                insImpAcc (M.insert n tm pnas) ps given imps'
            Nothing ->
              if inpat
                then PTacImplicit p l n sc Placeholder :
                  insImpAcc (M.insert n Placeholder pnas) ps given imps
                else PTacImplicit p l n sc sc :
                  insImpAcc (M.insert n sc pnas) ps given imps
    insImpAcc _ expected [] imps = map addUnknownImp imps -- so that unused implicits give error
    insImpAcc _ _        given imps = given ++ imps

    addUnknownImp arg = arg { argopts = UnknownImp : argopts arg }

    find n []               acc = Nothing
    find n (PImp _ _ _ n' t : gs) acc
         | n == n' = Just (t, reverse acc ++ gs)
    find n (PTacImplicit _ _ n' _ t : gs) acc
         | n == n' = Just (t, reverse acc ++ gs)
    find n (g : gs) acc = find n gs (g : acc)

-- | return True if the second argument is an implicit argument which
-- is expected in the implicits, or if it's not an implicit
impIn :: [PArg] -> PArg -> Bool
impIn ps (PExp _ _ _ _) = True
impIn ps (PConstraint  _ _ _ _) = True
impIn ps arg = any (\p -> not (expArg arg) && pname arg == pname p) ps

expArg (PExp _ _ _ _) = True
expArg (PConstraint _ _ _ _) = True
expArg _ = False

-- replace non-linear occurrences with _

stripLinear :: IState -> PTerm -> PTerm
stripLinear i tm = evalState (sl tm) [] where
    sl :: PTerm -> State [Name] PTerm
    sl (PRef fc hl f)
         | (_:_) <- lookupTy f (tt_ctxt i)
              = return $ PRef fc hl f
         | otherwise = do ns <- get
                          if (f `elem` ns)
                             then return $ PHidden (PRef fc hl f) -- Placeholder
                             else do put (f : ns)
                                     return (PRef fc hl f)
    sl (PPatvar fc f)
                     = do ns <- get
                          if (f `elem` ns)
                             then return $ PHidden (PPatvar fc f) -- Placeholder
                             else do put (f : ns)
                                     return (PPatvar fc f)
    -- Assumption is that variables are all the same in each alternative
    sl t@(PAlternative ms b as) = do ns <- get
                                     as' <- slAlts ns as
                                     return (PAlternative ms b as')
       where slAlts ns (a : as) = do put ns
                                     a' <- sl a
                                     as' <- slAlts ns as
                                     return (a' : as')
             slAlts ns [] = return []
    sl (PPair fc hls p l r) = do l' <- sl l; r' <- sl r; return (PPair fc hls p l' r')
    sl (PDPair fc hls p l t r) = do l' <- sl l
                                    t' <- sl t
                                    r' <- sl r
                                    return (PDPair fc hls p l' t' r')
    sl (PApp fc fn args) = do fn' <- case fn of
                                     -- Just the args, fn isn't matchable as a var
                                          PRef _ _ _ -> return fn
                                          t -> sl t
                              args' <- mapM slA args
                              return $ PApp fc fn' args'
       where slA (PImp p m l n t) = do t' <- sl t
                                       return $ PImp p m l n t'
             slA (PExp p l n t) = do  t' <- sl t
                                      return $ PExp p l n t'
             slA (PConstraint p l n t)
                                = do t' <- sl t
                                     return $ PConstraint p l n t'
             slA (PTacImplicit p l n sc t)
                                = do t' <- sl t
                                     return $ PTacImplicit p l n sc t'
    sl x = return x

-- | Remove functions which aren't applied to anything, which must then
-- be resolved by unification. Assume names resolved and alternatives
-- filled in (so no ambiguity).
stripUnmatchable :: IState -> PTerm -> PTerm
stripUnmatchable i (PApp fc fn args) = PApp fc fn (fmap (fmap su) args) where
    su :: PTerm -> PTerm
    su tm@(PRef fc hl f)
       | (Bind n (Pi _ _ t _) sc :_) <- lookupTy f (tt_ctxt i)
          = Placeholder
       | (TType _ : _) <- lookupTy f (tt_ctxt i),
         not (implicitable f)
          = PHidden tm
       | (UType _ : _) <- lookupTy f (tt_ctxt i),
         not (implicitable f)
          = PHidden tm
    su (PApp fc f@(PRef _ _ fn) args)
       -- here we use canBeDConName because the impossible pattern
       -- check will not necessarily fully resolve constructor names,
       -- and these bare names will otherwise get in the way of
       -- impossbility checking.
       | -- Just fn <- getFn f,
         canBeDConName fn ctxt
          = PApp fc f (fmap (fmap su) args)
      where getFn (PRef _ _ fn) = Just fn
            getFn (PApp _ f args) = getFn f
            getFn _ = Nothing
    su (PApp fc f args)
          = PHidden (PApp fc f args)
    su (PAlternative ms b alts)
       = let alts' = filter (/= Placeholder) (map su alts) in
             if null alts' then Placeholder
                           else liftHidden $ PAlternative ms b alts'
    su (PPair fc hls p l r) = PPair fc hls p (su l) (su r)
    su (PDPair fc hls p l t r) = PDPair fc hls p (su l) (su t) (su r)
    su t@(PLam fc _ _ _ _) = PHidden t
    su t@(PPi _ _ _ _ _) = PHidden t
    su t@(PConstant _ c) | isTypeConst c = PHidden t
    su t = t

    ctxt = tt_ctxt i

    -- If the ambiguous terms are all hidden, the PHidden needs to be outside
    -- because elaboration of PHidden gets delayed, and we need the elaboration
    -- to resolve the ambiguity.
    liftHidden tm@(PAlternative ms b as)
        | allHidden as = PHidden (PAlternative ms b (map unHide as))
        | otherwise = tm

    allHidden [] = True
    allHidden (PHidden _ : xs) = allHidden xs
    allHidden (x : xs) = False

    unHide (PHidden t) = t
    unHide t = t

stripUnmatchable i tm = tm

mkPApp fc a f [] = f
mkPApp fc a f as = let rest = drop a as in
                       if a == 0 then appRest fc f rest
                          else appRest fc (PApp fc f (take a as)) rest
  where
    appRest fc f [] = f
    appRest fc f (a : as) = appRest fc (PApp fc f [a]) as



-- | Find 'static' argument positions
-- (the declared ones, plus any names in argument position in the declared
-- statics)
-- FIXME: It's possible that this really has to happen after elaboration
findStatics :: IState -> PTerm -> (PTerm, [Bool])
findStatics ist tm = let (ns, ss) = fs tm
                     in runState (pos ns ss tm) []
  where fs (PPi p n fc t sc)
            | Static <- pstatic p
                        = let (ns, ss) = fs sc in
                              (namesIn [] ist t : ns, n : ss)
            | otherwise = let (ns, ss) = fs sc in
                              (ns, ss)
        fs _ = ([], [])

        inOne n ns = length (filter id (map (elem n) ns)) == 1

        pos ns ss (PPi p n fc t sc)
            | elem n ss = do sc' <- pos ns ss sc
                             spos <- get
                             put (True : spos)
                             return (PPi (p { pstatic = Static }) n fc t sc')
            | otherwise = do sc' <- pos ns ss sc
                             spos <- get
                             put (False : spos)
                             return (PPi p n fc t sc')
        pos ns ss t = return t

-- for 6.12/7 compatibility
data EitherErr a b = LeftErr a | RightOK b deriving ( Functor )

instance Applicative (EitherErr a) where
    pure  = return
    (<*>) = ap

instance Monad (EitherErr a) where
    return = RightOK

    (LeftErr e) >>= _ = LeftErr e
    RightOK v   >>= k = k v

toEither :: EitherErr a b -> Either a b
toEither (LeftErr e)  = Left e
toEither (RightOK ho) = Right ho

-- | Syntactic match of a against b, returning pair of variables in a
-- and what they match. Returns the pair that failed if not a match.
matchClause :: IState -> PTerm -> PTerm -> Either (PTerm, PTerm) [(Name, PTerm)]
matchClause = matchClause' False

matchClause' :: Bool -> IState -> PTerm -> PTerm -> Either (PTerm, PTerm) [(Name, PTerm)]
matchClause' names i x y = checkRpts $ match (fullApp x) (fullApp y) where
    matchArg x y = match (fullApp (getTm x)) (fullApp (getTm y))

    fullApp (PApp _ (PApp fc f args) xs) = fullApp (PApp fc f (args ++ xs))
    fullApp x = x

    match' x y = match (fullApp x) (fullApp y)
    match (PApp _ (PRef _ _ (NS (UN fi) [b])) [_,_,x]) x'
        | fi == txt "fromInteger" && b == txt "builtins",
          PConstant _ (I _) <- getTm x = match (getTm x) x'
    match x' (PApp _ (PRef _ _ (NS (UN fi) [b])) [_,_,x])
        | fi == txt "fromInteger" && b == txt "builtins",
          PConstant _ (I _) <- getTm x = match (getTm x) x'
    match (PApp _ (PRef _ _ (UN l)) [_,x]) x' | l == txt "lazy" = match (getTm x) x'
    match x (PApp _ (PRef _ _ (UN l)) [_,x']) | l == txt "lazy" = match x (getTm x')
    match (PApp _ f args) (PApp _ f' args')
        | length args == length args'
            = do mf <- match' f f'
                 ms <- zipWithM matchArg args args'
                 return (mf ++ concat ms)
    match (PRef f hl n) (PApp _ x []) = match (PRef f hl n) x
    match (PPatvar f n) xr = match (PRef f [f] n) xr
    match xr (PPatvar f n) = match xr (PRef f [f] n)
    match (PApp _ x []) (PRef f hl n) = match x (PRef f hl n)
    match (PRef _ _ n) tm@(PRef _ _ n')
        | n == n' && not names &&
          (not (isConName n (tt_ctxt i) || isFnName n (tt_ctxt i))
                || tm == Placeholder)
            = return [(n, tm)]
        -- if one namespace is missing, drop the other
        | n == n' || n == dropNS n' || dropNS n == n' = return []
       where dropNS (NS n _) = n
             dropNS n = n
    match (PRef _ _ n) tm
        | not names && (not (isConName n (tt_ctxt i) ||
                             isFnName n (tt_ctxt i)) || tm == Placeholder)
            = return [(n, tm)]
    match (PRewrite _ by l r _) (PRewrite _ by' l' r' _) | by == by'
                                    = do ml <- match' l l'
                                         mr <- match' r r'
                                         return (ml ++ mr)
    match (PTyped l r) (PTyped l' r') = do ml <- match l l'
                                           mr <- match r r'
                                           return (ml ++ mr)
    match (PTyped l r) x = match l x
    match x (PTyped l r) = match x l
    match (PPair _ _ _ l r) (PPair _ _ _ l' r') = do ml <- match' l l'
                                                     mr <- match' r r'
                                                     return (ml ++ mr)
    match (PDPair _ _ _ l t r) (PDPair _ _ _ l' t' r') = do ml <- match' l l'
                                                            mt <- match' t t'
                                                            mr <- match' r r'
                                                            return (ml ++ mt ++ mr)
    match (PAlternative _ a as) (PAlternative _ a' as')
        = do ms <- zipWithM match' as as'
             return (concat ms)
    match a@(PAlternative _ _ as) b
        = do let ms = zipWith match' as (repeat b)
             case (rights (map toEither ms)) of
                (x: _) -> return x
                _ -> LeftErr (a, b)
    match (PCase _ _ _) _ = return [] -- lifted out
    match (PMetavar _ _) _ = return [] -- modified
    match (PInferRef _ _ _) _ = return [] -- modified
    match (PQuote _) _ = return []
    match (PProof _) _ = return []
    match (PTactics _) _ = return []
    match (PResolveTC _) (PResolveTC _) = return []
    match (PTrue _ _) (PTrue _ _) = return []
    match (PPi _ _ _ t s) (PPi _ _ _ t' s') = do mt <- match' t t'
                                                 ms <- match' s s'
                                                 return (mt ++ ms)
    match (PLam _ _ _ t s) (PLam _ _ _ t' s') = do mt <- match' t t'
                                                   ms <- match' s s'
                                                   return (mt ++ ms)
    match (PLet _ _ _ t ty s) (PLet _ _ _ t' ty' s') = do mt <- match' t t'
                                                          mty <- match' ty ty'
                                                          ms <- match' s s'
                                                          return (mt ++ mty ++ ms)
    match (PHidden x) (PHidden y)
          | RightOK xs <- match x y = return xs -- to collect variables
          | otherwise = return [] -- Otherwise hidden things are unmatchable
    match (PHidden x) y
          | RightOK xs <- match x y = return xs
          | otherwise = return []
    match x (PHidden y)
          | RightOK xs <- match x y = return xs
          | otherwise = return []
    match (PUnifyLog x) y = match' x y
    match x (PUnifyLog y) = match' x y
    match (PNoImplicits x) y = match' x y
    match x (PNoImplicits y) = match' x y
    match Placeholder _ = return []
    match _ Placeholder = return []
    match (PResolveTC _) _ = return []
    match a b | a == b = return []
              | otherwise = LeftErr (a, b)

    checkRpts (RightOK ms) = check ms where
        check ((n,t):xs)
            | Just t' <- lookup n xs = if t/=t' && t/=Placeholder && t'/=Placeholder
                                                then Left (t, t')
                                                else check xs
        check (_:xs) = check xs
        check [] = Right ms
    checkRpts (LeftErr x) = Left x

substMatches :: [(Name, PTerm)] -> PTerm -> PTerm
substMatches ms = substMatchesShadow ms []

-- substMatchesShadow :: [(Name, PTerm)] -> [Name] -> PTerm -> PTerm
-- substMatchesShadow [] shs t = t
-- substMatchesShadow ((n,tm):ns) shs t
--    = substMatchShadow n shs tm (substMatchesShadow ns shs t)

substMatch :: Name -> PTerm -> PTerm -> PTerm
substMatch n = substMatchShadow n []

substMatchShadow :: Name -> [Name] -> PTerm -> PTerm -> PTerm
substMatchShadow n shs tm t = substMatchesShadow [(n, tm)] shs t

substMatchesShadow :: [(Name, PTerm)] -> [Name] -> PTerm -> PTerm
substMatchesShadow nmap shs t = sm shs t where
    sm xs (PRef _ _ n) | Just tm <- lookup n nmap = tm
    sm xs (PLam fc x xfc t sc) = PLam fc x xfc (sm xs t) (sm xs sc)
    sm xs (PPi p x fc t sc)
         | x `elem` xs
             = let x' = nextName x in
                   PPi p x' fc (sm (x':xs) (substMatch x (PRef emptyFC [] x') t))
                               (sm (x':xs) (substMatch x (PRef emptyFC [] x') sc))
         | otherwise = PPi p x fc (sm xs t) (sm (x : xs) sc)
    sm xs (PLet fc x xfc val t sc)
         = PLet fc x xfc (sm xs val) (sm xs t) (sm xs sc)
    sm xs (PApp f x as) = fullApp $ PApp f (sm xs x) (map (fmap (sm xs)) as)
    sm xs (PCase f x as) = PCase f (sm xs x) (map (pmap (sm xs)) as)
    sm xs (PIfThenElse fc c t f) = PIfThenElse fc (sm xs c) (sm xs t) (sm xs f)
    sm xs (PRewrite f by x y tm) = PRewrite f by (sm xs x) (sm xs y)
                                                 (fmap (sm xs) tm)
    sm xs (PTyped x y) = PTyped (sm xs x) (sm xs y)
    sm xs (PPair f hls p x y) = PPair f hls p (sm xs x) (sm xs y)
    sm xs (PDPair f hls p x t y) = PDPair f hls p (sm xs x) (sm xs t) (sm xs y)
    sm xs (PAlternative ms a as) = PAlternative ms a (map (sm xs) as)
    sm xs (PHidden x) = PHidden (sm xs x)
    sm xs (PUnifyLog x) = PUnifyLog (sm xs x)
    sm xs (PNoImplicits x) = PNoImplicits (sm xs x)
    sm xs (PRunElab fc script ns) = PRunElab fc (sm xs script) ns
    sm xs (PConstSugar fc tm) = PConstSugar fc (sm xs tm)
    sm xs x = x

    fullApp (PApp _ (PApp fc f args) xs) = fullApp (PApp fc f (args ++ xs))
    fullApp x = x

shadow :: Name -> Name -> PTerm -> PTerm
shadow n n' t = sm 0 t where
    sm 0 (PRef fc hl x) | n == x = PRef fc hl n'
    sm 0 (PLam fc x xfc t sc) | n /= x = PLam fc x xfc (sm 0 t) (sm 0 sc)
                            | otherwise = PLam fc x xfc (sm 0 t) sc
    sm 0 (PPi p x fc t sc) | n /= x = PPi p x fc (sm 0 t) (sm 0 sc)
                         | otherwise = PPi p x fc (sm 0 t) sc
    sm 0 (PLet fc x xfc t v sc) | n /= x = PLet fc x xfc (sm 0 t) (sm 0 v) (sm 0 sc)
                              | otherwise = PLet fc x xfc (sm 0 t) (sm 0 v) sc
    sm 0 (PApp f x as) = PApp f (sm 0 x) (map (fmap (sm 0)) as)
    sm 0 (PAppBind f x as) = PAppBind f (sm 0 x) (map (fmap (sm 0)) as)
    sm 0 (PCase f x as) = PCase f (sm 0 x) (map (pmap (sm 0)) as)
    sm 0 (PIfThenElse fc c t f) = PIfThenElse fc (sm 0 c) (sm 0 t) (sm 0 f)
    sm 0 (PRewrite f by x y tm) = PRewrite f by (sm 0 x) (sm 0 y) (fmap (sm 0) tm)
    sm 0 (PTyped x y) = PTyped (sm 0 x) (sm 0 y)
    sm 0 (PPair f hls p x y) = PPair f hls p (sm 0 x) (sm 0 y)
    sm 0 (PDPair f hls p x t y) = PDPair f hls p (sm 0 x) (sm 0 t) (sm 0 y)
    sm 0 (PAlternative ms a as)
          = PAlternative (map shadowAlt ms) a (map (sm 0) as)
    sm 0 (PTactics ts) = PTactics (map (fmap (sm 0)) ts)
    sm 0 (PProof ts) = PProof (map (fmap (sm 0)) ts)
    sm 0 (PHidden x) = PHidden (sm 0 x)
    sm 0 (PUnifyLog x) = PUnifyLog (sm 0 x)
    sm 0 (PNoImplicits x) = PNoImplicits (sm 0 x)
    sm 0 (PCoerced t) = PCoerced (sm 0 t)
    sm ql (PQuasiquote tm ty) = PQuasiquote (sm (ql + 1) tm) (fmap (sm ql) ty)
    sm ql (PUnquote tm) = PUnquote (sm (ql - 1) tm)
    sm ql x = descend (sm ql) x

    shadowAlt p@(x, oldn) = (update x, update oldn)
    update oldn | n == oldn = n'
                | otherwise = oldn

-- | Rename any binders which are repeated (so that we don't have to
-- mess about with shadowing anywhere else).
mkUniqueNames :: [Name] -> [(Name, Name)] -> PTerm -> PTerm
mkUniqueNames env shadows tm
      = evalState (mkUniq 0 initMap tm) (S.fromList env) where

  initMap = M.fromList shadows

  inScope :: S.Set Name
  inScope = S.fromList $ boundNamesIn tm

  mkUniqA ql nmap arg = do t' <- mkUniq ql nmap (getTm arg)
                           return (arg { getTm = t' })

  -- Initialise the unique name with the environment length (so we're not
  -- looking for too long...)
  initN (UN n) l = UN $ txt (str n ++ show l)
  initN (MN i s) l = MN (i+l) s
  initN n _ = n

  -- FIXME: Probably ought to do this for completeness! It's fine as
  -- long as there are no bindings inside tactics though.
  mkUniqT _ nmap tac = return tac

  mkUniq :: Int -- ^ The number of quotations that we're under
         -> M.Map Name Name -> PTerm -> State (S.Set Name) PTerm
  mkUniq 0 nmap (PLam fc n nfc ty sc)
         = do env <- get
              (n', sc') <-
                    if n `S.member` env
                       then do let n' = uniqueNameSet (initN n (S.size env))
                                                      (S.union env inScope)
                               return (n', sc) -- shadow n n' sc)
                       else return (n, sc)
              put (S.insert n' env)
              let nmap' = M.insert n n' nmap
              ty' <- mkUniq 0 nmap ty
              sc'' <- mkUniq 0 nmap' sc'
              return $! PLam fc n' nfc ty' sc''
  mkUniq 0 nmap (PPi p n fc ty sc)
         = do env <- get
              (n', sc') <-
                    if n `S.member` env
                       then do let n' = uniqueNameSet (initN n (S.size env))
                                                      (S.union env inScope)
                               return (n', sc) -- shadow n n' sc)
                       else return (n, sc)
              put (S.insert n' env)
              let nmap' = M.insert n n' nmap
              ty' <- mkUniq 0 nmap ty
              sc'' <- mkUniq 0 nmap' sc'
              return $! PPi p n' fc ty' sc''
  mkUniq 0 nmap (PLet fc n nfc ty val sc)
         = do env <- get
              (n', sc') <-
                    if n `S.member` env
                       then do let n' = uniqueNameSet (initN n (S.size env))
                                                      (S.union env inScope)
                               return (n', sc) -- shadow n n' sc)
                       else return (n, sc)
              put (S.insert n' env)
              let nmap' = M.insert n n' nmap
              ty' <- mkUniq 0 nmap ty; val' <- mkUniq 0 nmap val
              sc'' <- mkUniq 0 nmap' sc'
              return $! PLet fc n' nfc ty' val' sc''
  mkUniq 0 nmap (PApp fc t args)
         = do t' <- mkUniq 0 nmap t
              args' <- mapM (mkUniqA 0 nmap) args
              return $! PApp fc t' args'
  mkUniq 0 nmap (PAppBind fc t args)
         = do t' <- mkUniq 0 nmap t
              args' <- mapM (mkUniqA 0 nmap) args
              return $! PAppBind fc t' args'
  mkUniq 0 nmap (PCase fc t alts)
         = do t' <- mkUniq 0 nmap t
              alts' <- mapM (\(x,y)-> do x' <- mkUniq 0 nmap x; y' <- mkUniq 0 nmap y
                                         return (x', y')) alts
              return $! PCase fc t' alts'
  mkUniq 0 nmap (PIfThenElse fc c t f)
         = liftM3 (PIfThenElse fc) (mkUniq 0 nmap c) (mkUniq 0 nmap t) (mkUniq 0 nmap f)
  mkUniq 0 nmap (PPair fc hls p l r)
         = do l' <- mkUniq 0 nmap l; r' <- mkUniq 0 nmap r
              return $! PPair fc hls p l' r'
  mkUniq 0 nmap (PDPair fc hls p (PRef fc' hls' n) t sc)
      | t /= Placeholder
         = do env <- get
              (n', sc') <- if n `S.member` env
                              then do let n' = uniqueNameSet n (S.union env inScope)
                                      return (n', sc) -- shadow n n' sc)
                              else return (n, sc)
              put (S.insert n' env)
              let nmap' = M.insert n n' nmap
              t' <- mkUniq 0 nmap t
              sc'' <- mkUniq 0 nmap' sc'
              return $! PDPair fc hls p (PRef fc' hls' n') t' sc''
  mkUniq 0 nmap (PDPair fc hls p l t r)
         = do l' <- mkUniq 0 nmap l; t' <- mkUniq 0 nmap t; r' <- mkUniq 0 nmap r
              return $! PDPair fc hls p l' t' r'
  mkUniq 0 nmap (PAlternative ns b as)
         -- store the nmap and defer the rest until we've pruned the set
         -- during elaboration
         = return $ PAlternative (ns ++ M.toList nmap) b as
  mkUniq 0 nmap (PHidden t) = liftM PHidden (mkUniq 0 nmap t)
  mkUniq 0 nmap (PUnifyLog t) = liftM PUnifyLog (mkUniq 0 nmap t)
  mkUniq 0 nmap (PDisamb n t) = liftM (PDisamb n) (mkUniq 0 nmap t)
  mkUniq 0 nmap (PNoImplicits t) = liftM PNoImplicits (mkUniq 0 nmap t)
  mkUniq 0 nmap (PProof ts) = liftM PProof (mapM (mkUniqT 0 nmap) ts)
  mkUniq 0 nmap (PTactics ts) = liftM PTactics (mapM (mkUniqT 0 nmap) ts)
  mkUniq 0 nmap (PRunElab fc ts ns) = liftM (\tm -> PRunElab fc tm ns) (mkUniq 0 nmap ts)
  mkUniq 0 nmap (PConstSugar fc tm) = liftM (PConstSugar fc) (mkUniq 0 nmap tm)
  mkUniq 0 nmap (PCoerced tm) = liftM PCoerced (mkUniq 0 nmap tm)
  mkUniq 0 nmap t = return $ shadowAll (M.toList nmap) t
    where
      shadowAll [] t = t
      shadowAll ((n, n') : ns) t = shadow n n' (shadowAll ns t)

  mkUniq ql nmap (PQuasiquote tm ty) =
    do tm' <- mkUniq (ql + 1) nmap tm
       ty' <- case ty of
                Nothing -> return Nothing
                Just t -> fmap Just $ mkUniq ql nmap t
       return $! PQuasiquote tm' ty'
  mkUniq ql nmap (PUnquote tm) = fmap PUnquote (mkUniq (ql - 1) nmap tm)

  mkUniq ql nmap tm = descendM (mkUniq ql nmap) tm

getFile :: Opt -> Maybe String
getFile (Filename s) = Just s
getFile _ = Nothing

getBC :: Opt -> Maybe String
getBC (BCAsm s) = Just s
getBC _ = Nothing

getOutput :: Opt -> Maybe String
getOutput (Output s) = Just s
getOutput _ = Nothing

getIBCSubDir :: Opt -> Maybe String
getIBCSubDir (IBCSubDir s) = Just s
getIBCSubDir _ = Nothing

getImportDir :: Opt -> Maybe String
getImportDir (ImportDir s) = Just s
getImportDir _ = Nothing

getSourceDir :: Opt -> Maybe String
getSourceDir (SourceDir s) = Just s
getSourceDir _ = Nothing

getPkgDir :: Opt -> Maybe String
getPkgDir (Pkg s) = Just s
getPkgDir _ = Nothing

getPkg :: Opt -> Maybe (Bool, String)
getPkg (PkgBuild s)   = Just (False, s)
getPkg (PkgInstall s) = Just (True, s)
getPkg _ = Nothing

getPkgClean :: Opt -> Maybe String
getPkgClean (PkgClean s) = Just s
getPkgClean _ = Nothing

getPkgREPL :: Opt -> Maybe String
getPkgREPL (PkgREPL s) = Just s
getPkgREPL _ = Nothing

getPkgCheck :: Opt -> Maybe String
getPkgCheck (PkgCheck s) = Just s
getPkgCheck _              = Nothing

-- | Returns None if given an Opt which is not PkgMkDoc
--   Otherwise returns Just x, where x is the contents of PkgMkDoc
getPkgMkDoc :: Opt                  -- ^ Opt to extract
            -> Maybe (Bool, String) -- ^ Result
getPkgMkDoc (PkgDocBuild  str)  = Just (False,str)
getPkgMkDoc (PkgDocInstall str) = Just (True,str)
getPkgMkDoc _              = Nothing

getPkgTest :: Opt          -- ^ the option to extract
           -> Maybe String -- ^ the package file to test
getPkgTest (PkgTest f) = Just f
getPkgTest _ = Nothing

getCodegen :: Opt -> Maybe Codegen
getCodegen (UseCodegen x) = Just x
getCodegen _ = Nothing

getCodegenArgs :: Opt -> Maybe String
getCodegenArgs (CodegenArgs args) = Just args
getCodegenArgs _ = Nothing

getConsoleWidth :: Opt -> Maybe ConsoleWidth
getConsoleWidth (UseConsoleWidth x) = Just x
getConsoleWidth _ = Nothing

getExecScript :: Opt -> Maybe String
getExecScript (InterpretScript expr) = Just expr
getExecScript _ = Nothing

getPkgIndex :: Opt -> Maybe FilePath
getPkgIndex (PkgIndex file) = Just file
getPkgIndex _ = Nothing

getEvalExpr :: Opt -> Maybe String
getEvalExpr (EvalExpr expr) = Just expr
getEvalExpr _ = Nothing

getOutputTy :: Opt -> Maybe OutputType
getOutputTy (OutputTy t) = Just t
getOutputTy _ = Nothing

getLanguageExt :: Opt -> Maybe LanguageExt
getLanguageExt (Extension e) = Just e
getLanguageExt _ = Nothing

getTriple :: Opt -> Maybe String
getTriple (TargetTriple x) = Just x
getTriple _ = Nothing

getCPU :: Opt -> Maybe String
getCPU (TargetCPU x) = Just x
getCPU _ = Nothing

getOptLevel :: Opt -> Maybe Int
getOptLevel (OptLevel x) = Just x
getOptLevel _ = Nothing

getOptimisation :: Opt -> Maybe (Bool,Optimisation)
getOptimisation (AddOpt p)    = Just (True,  p)
getOptimisation (RemoveOpt p) = Just (False, p)
getOptimisation _             = Nothing

getColour :: Opt -> Maybe Bool
getColour (ColourREPL b) = Just b
getColour _ = Nothing

getClient :: Opt -> Maybe String
getClient (Client x) = Just x
getClient _ = Nothing

-- Get the first valid port
getPort :: [Opt] -> Maybe REPLPort
getPort []            = Nothing
getPort (Port p : _ ) = Just p
getPort (_      : xs) = getPort xs

opt :: (Opt -> Maybe a) -> [Opt] -> [a]
opt = mapMaybe

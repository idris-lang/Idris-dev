{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             TypeSynonymInstances, PatternGuards #-}

module Idris.AbsSyntax(module Idris.AbsSyntax, module Idris.AbsSyntaxTree) where

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Typecheck
import Idris.AbsSyntaxTree
import Idris.Colours
import Idris.IdeSlave
import IRTS.CodegenCommon
import Util.DynamicLinker

import Paths_idris

import System.Console.Haskeline
import System.IO

import Control.Monad.State
import Control.Monad.Error(throwError)

import Data.List
import Data.Char
import qualified Data.Text as T
import Data.Either
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.Word (Word)

import Debug.Trace

import Control.Monad.Error (throwError, catchError)
import System.IO.Error(isUserError, ioeGetErrorString, tryIOError)

import Util.Pretty
import Util.ScreenSize
import Util.System

getContext :: Idris Context
getContext = do i <- getIState; return (tt_ctxt i)

forCodegen :: Codegen -> [(Codegen, a)] -> [a]
forCodegen tgt xs = [x | (tgt', x) <- xs, tgt == tgt']

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
                   case mapMaybe (findDyLib ls) libs of
                     x:_ -> return (Left x)
                     [] -> do
                       handle <- lift . lift $ mapM (\l -> catchIO (tryLoadLib l) (\_ -> return Nothing)) $ libs
                       case msum handle of
                         Nothing -> return (Right $ "Could not load dynamic alternatives \"" ++
                                                    concat (intersperse "," libs) ++ "\"")
                         Just x -> do putIState $ i { idris_dynamic_libs = x:ls }
                                      return (Left x)
    where findDyLib :: [DynamicLib] -> String -> Maybe DynamicLib
          findDyLib []         l                     = Nothing
          findDyLib (lib:libs) l | l == lib_name lib = Just lib
                                 | otherwise         = findDyLib libs l


addHdr :: Codegen -> String -> Idris ()
addHdr tgt f = do i <- getIState; putIState $ i { idris_hdrs = nub $ (tgt, f) : idris_hdrs i }

addLangExt :: LanguageExt -> Idris ()
addLangExt TypeProviders = do i <- getIState
                              putIState $ i {
                                idris_language_extensions = TypeProviders : idris_language_extensions i
                              }
addLangExt ErrorReflection = do i <- getIState
                                putIState $ i {
                                  idris_language_extensions = ErrorReflection : idris_language_extensions i
                                }

addTrans :: (Term, Term) -> Idris ()
addTrans t = do i <- getIState
                putIState $ i { idris_transforms = t : idris_transforms i }

addErrRev :: (Term, Term) -> Idris ()
addErrRev t = do i <- getIState
                 putIState $ i { idris_errRev = t : idris_errRev i }

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

setAccessibility :: Name -> Accessibility -> Idris ()
setAccessibility n a
         = do i <- getIState
              let ctxt = setAccess n a (tt_ctxt i)
              putIState $ i { tt_ctxt = ctxt }

setTotality :: Name -> Totality -> Idris ()
setTotality n a
         = do i <- getIState
              let ctxt = setTotal n a (tt_ctxt i)
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
    where findCoercions t [] = []
          findCoercions t (n : ns) =
             let ps = case lookupTy n (tt_ctxt i) of
                        [ty'] -> case unApply (getRetTy ty') of
                                   (t', _) ->
                                      if t == t' then [n] else []
                        _ -> [] in
                 ps ++ findCoercions t ns

addToCG :: Name -> CGInfo -> Idris ()
addToCG n cg
   = do i <- getIState
        putIState $ i { idris_callgraph = addDef n cg (idris_callgraph i) }

-- | Adds error handlers for a particular function and argument. If names are is ambiguous, all matching handlers are updated.
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

getFunctionErrorHandlers :: Name -> Name -> Idris [Name]
getFunctionErrorHandlers f arg = do i <- getIState
                                    return . maybe [] S.toList $
                                     undefined --lookup arg =<< lookupCtxtExact f (idris_function_errorhandlers i)


-- Trace all the names in a call graph starting at the given name
getAllNames :: Name -> Idris [Name]
getAllNames n = allNames [] n

allNames :: [Name] -> Name -> Idris [Name]
allNames ns n | n `elem` ns = return []
allNames ns n = do i <- getIState
                   case lookupCtxtExact n (idris_callgraph i) of
                      Just ns' -> do more <- mapM (allNames (n:ns)) (map fst (calls ns'))
                                     return (nub (n : concat more))
                      _ -> return [n]

addCoercion :: Name -> Idris ()
addCoercion n = do i <- getIState
                   putIState $ i { idris_coercions = nub $ n : idris_coercions i }

addDocStr :: Name -> String -> Idris ()
addDocStr n doc
   = do i <- getIState
        putIState $ i { idris_docstrings = addDef n doc (idris_docstrings i) }

addNameHint :: Name -> Name -> Idris ()
addNameHint ty n
   = do i <- getIState
        ty' <- case lookupCtxtName ty (idris_implicits i) of
                       [(tyn, _)] -> return tyn
                       [] -> throwError (NoSuchVariable ty)
                       tyns -> throwError (CantResolveAlts (map show (map fst tyns)))
        let ns' = case lookupCtxt ty' (idris_namehints i) of
                       [ns] -> ns ++ [n]
                       _ -> [n]
        putIState $ i { idris_namehints = addDef ty' ns' (idris_namehints i) }

getNameHints :: IState -> Name -> [Name]
getNameHints i (UN arr) | arr == txt "->" = [sUN "f",sUN "g"]
getNameHints i n =
        case lookupCtxt n (idris_namehints i) of
             [ns] -> ns
             _ -> []

addToCalledG :: Name -> [Name] -> Idris ()
addToCalledG n ns = return () -- TODO

-- Add a class instance function. Dodgy hack: Put integer instances first in the
-- list so they are resolved by default.
-- Dodgy hack 2: put constraint chasers (@@) last

addInstance :: Bool -> Name -> Name -> Idris ()
addInstance int n i
    = do ist <- getIState
         case lookupCtxt n (idris_classes ist) of
                [CI a b c d e ins] ->
                     do let cs = addDef n (CI a b c d e (addI i ins)) (idris_classes ist)
                        putIState $ ist { idris_classes = cs }
                _ -> do let cs = addDef n (CI (sMN 0 "none") [] [] [] [] [i]) (idris_classes ist)
                        putIState $ ist { idris_classes = cs }
  where addI i ins | int = i : ins
                   | chaser n = ins ++ [i]
                   | otherwise = insI i ins
        insI i [] = [i]
        insI i (n : ns) | chaser n = i : n : ns
                        | otherwise = n : insI i ns

        chaser (UN nm) 
             | ('@':'@':_) <- str nm = True
        chaser (NS n _) = chaser n
        chaser _ = False

addClass :: Name -> ClassInfo -> Idris ()
addClass n i
   = do ist <- getIState
        let i' = case lookupCtxt n (idris_classes ist) of
                      [c] -> c { class_instances = class_instances i }
                      _ -> i
        putIState $ ist { idris_classes = addDef n i' (idris_classes ist) }

addIBC :: IBCWrite -> Idris ()
addIBC ibc@(IBCDef n)
           = do i <- getIState
                when (notDef (ibc_write i)) $
                  putIState $ i { ibc_write = ibc : ibc_write i }
   where notDef [] = True
         notDef (IBCDef n': is) | n == n' = False
         notDef (_ : is) = notDef is
addIBC ibc = do i <- getIState; putIState $ i { ibc_write = ibc : ibc_write i }

clearIBC :: Idris ()
clearIBC = do i <- getIState; putIState $ i { ibc_write = [] }

resetNameIdx :: Idris ()
resetNameIdx = do i <- getIState
                  put (i { idris_nameIdx = (0, emptyContext) })

-- Used to preserve sharing of names
addNameIdx :: Name -> Idris (Int, Name)
addNameIdx n = do i <- getIState
                  let (i', x) = addNameIdx' i n
                  return x

addNameIdx' :: IState -> Name -> (IState, (Int, Name))
addNameIdx' i n
   = let idxs = snd (idris_nameIdx i) in
         case lookupCtxt n idxs of
            [x] -> (i, x)
            _ -> let i' = fst (idris_nameIdx i) + 1 in
                    (i { idris_nameIdx = (i', addDef n (i', n) idxs) }, (i', n))

getHdrs :: Codegen -> Idris [String]
getHdrs tgt = do i <- getIState; return (forCodegen tgt $ idris_hdrs i)

setErrLine :: Int -> Idris ()
setErrLine x = do i <- getIState;
                  case (errLine i) of
                      Nothing -> putIState $ i { errLine = Just x }
                      Just _ -> return ()

clearErr :: Idris ()
clearErr = do i <- getIState
              putIState $ i { errLine = Nothing }

getSO :: Idris (Maybe String)
getSO = do i <- getIState
           return (compiled_so i)

setSO :: Maybe String -> Idris ()
setSO s = do i <- getIState
             putIState $ (i { compiled_so = s })

getIState :: Idris IState
getIState = get

putIState :: IState -> Idris ()
putIState = put

-- | A version of liftIO that puts errors into the exception type of the Idris monad
runIO :: IO a -> Idris a
runIO x = liftIO (tryIOError x) >>= either (throwError . Msg . show) return
-- TODO: create specific Idris exceptions for specific IO errors such as "openFile: does not exist"

getName :: Idris Int
getName = do i <- getIState;
             let idx = idris_name i;
             putIState $ (i { idris_name = idx + 1 })
             return idx

addInternalApp :: FilePath -> Int -> PTerm -> Idris ()
addInternalApp fp l t
    = do i <- getIState
         putIState (i { idris_lineapps = ((fp, l), t) : idris_lineapps i })

getInternalApp :: FilePath -> Int -> Idris PTerm
getInternalApp fp l = do i <- getIState
                         case lookup (fp, l) (idris_lineapps i) of
                              Just n' -> return n'
                              Nothing -> return Placeholder
                              -- TODO: What if it's not there?

-- Pattern definitions are only used for coverage checking, so erase them
-- when we're done
clearOrigPats :: Idris ()
clearOrigPats = do i <- get
                   let ps = idris_patdefs i
                   let ps' = mapCtxt (\ (_,miss) -> ([], miss)) ps
                   put (i { idris_patdefs = ps' })

-- Erase types from Ps in the context (basically ending up with what's in
-- the .ibc, which is all we need after all the analysis is done)
clearPTypes :: Idris ()
clearPTypes = do i <- get
                 let ctxt = tt_ctxt i 
                 put (i { tt_ctxt = mapDefCtxt pErase ctxt })
   where pErase (CaseOp c t tys orig tot cds) 
            = CaseOp c t tys orig [] (pErase' cds)
         pErase x = x
         pErase' (CaseDefs _ (cs, c) _ rs)
             = let c' = (cs, fmap pEraseType c) in
                   CaseDefs c' c' c' rs

checkUndefined :: FC -> Name -> Idris ()
checkUndefined fc n
    = do i <- getContext
         case lookupTy n i of
             (_:_)  -> throwError . Msg $ show fc ++ ":" ++
                                          show n ++ " already defined"
             _ -> return ()

isUndefined :: FC -> Name -> Idris Bool
isUndefined fc n
    = do i <- getContext
         case lookupTy n i of
             (_:_)  -> return False
             _ -> return True

setContext :: Context -> Idris ()
setContext ctxt = do i <- getIState; putIState $ (i { tt_ctxt = ctxt } )

updateContext :: (Context -> Context) -> Idris ()
updateContext f = do i <- getIState; putIState $ (i { tt_ctxt = f (tt_ctxt i) } )

addConstraints :: FC -> (Int, [UConstraint]) -> Idris ()
addConstraints fc (v, cs)
    = do i <- getIState
         let ctxt = tt_ctxt i
         let ctxt' = ctxt { uconstraints = cs ++ uconstraints ctxt,
                            next_tvar = v }
         let ics = zip cs (repeat fc) ++ idris_constraints i
         putIState $ i { tt_ctxt = ctxt', idris_constraints = ics }

addDeferred = addDeferred' Ref
addDeferredTyCon = addDeferred' (TCon 0 0)

addDeferred' :: NameType -> [(Name, (Int, Maybe Name, Type, Bool))] -> Idris ()
addDeferred' nt ns
  = do mapM_ (\(n, (i, _, t, _)) -> updateContext (addTyDecl n nt (tidyNames [] t))) ns
       i <- getIState
       putIState $ i { idris_metavars = map (\(n, (i, top, _, isTopLevel)) -> (n, (top, i, isTopLevel))) ns ++
                                            idris_metavars i }
  where tidyNames used (Bind (MN i x) b sc)
            = let n' = uniqueName (UN x) used in
                  Bind n' b $ tidyNames (n':used) sc
        tidyNames used (Bind n b sc)
            = let n' = uniqueName n used in
                  Bind n' b $ tidyNames (n':used) sc
        tidyNames used b = b

solveDeferred :: Name -> Idris ()
solveDeferred n = do i <- getIState
                     putIState $ i { idris_metavars =
                                       filter (\(n', _) -> n/=n')
                                          (idris_metavars i) }

getUndefined :: Idris [Name]
getUndefined = do i <- getIState
                  return (map fst (idris_metavars i) \\ primDefs)

getWidth :: Idris ConsoleWidth
getWidth = fmap idris_consolewidth getIState

setWidth :: ConsoleWidth -> Idris ()
setWidth w = do ist <- getIState
                put ist { idris_consolewidth = w }

renderWidth :: Idris Int
renderWidth = do iw <- getWidth
                 case iw of
                   InfinitelyWide -> return 100000000
                   ColsWide n -> return (max n 1)
                   AutomaticWidth -> runIO getScreenWidth


iRender :: Doc a -> Idris (SimpleDoc a)
iRender d = do w <- getWidth
               case w of
                 InfinitelyWide -> return $ renderPretty 1.0 1000000000 d
                 ColsWide n -> return $
                               if n < 1
                                 then renderPretty 1.0 1000000000 d
                                 else renderPretty 0.8 n d
                 AutomaticWidth -> do width <- runIO getScreenWidth
                                      return $ renderPretty 0.8 width d

ihPrintResult :: Handle -> String -> Idris ()
ihPrintResult h s = do i <- getIState
                       case idris_outputmode i of
                         RawOutput -> case s of
                                        "" -> return ()
                                        s  -> runIO $ hPutStrLn h s
                         IdeSlave n ->
                             let good = SexpList [SymbolAtom "ok", toSExp s] in
                             runIO $ hPutStrLn h $ convSExp "return" good n

-- | Write a pretty-printed term to the console with semantic coloring
consoleDisplayAnnotated :: Handle -> Doc OutputAnnotation -> Idris ()
consoleDisplayAnnotated h output = do ist <- getIState
                                      rendered <- iRender $ output
                                      runIO . hPutStrLn h .
                                        displayDecorated (consoleDecorate ist) $
                                        rendered


-- | Write pretty-printed output to IDESlave with semantic annotations
ideSlaveReturnAnnotated :: Integer -> Handle -> Doc OutputAnnotation -> Idris ()
ideSlaveReturnAnnotated n h out = do ist <- getIState
                                     let (str, spans) = displaySpans .
                                                        renderPretty 0.8 80 .
                                                        fmap (fancifyAnnots ist) $
                                                        out
                                         good = [SymbolAtom "ok", toSExp str, toSExp spans]
                                     runIO . hPutStrLn h $ convSExp "return" good n

ihPrintTermWithType :: Handle -> Doc OutputAnnotation -> Doc OutputAnnotation -> Idris ()
ihPrintTermWithType h tm ty = do ist <- getIState
                                 let output = tm <+> colon <+> ty
                                 case idris_outputmode ist of
                                   RawOutput -> consoleDisplayAnnotated h output
                                   IdeSlave n -> ideSlaveReturnAnnotated n h output

-- | Pretty-print a collection of overloadings to REPL or IDESlave - corresponds to :t name
ihPrintFunTypes :: Handle -> Name -> [(Name, PTerm)] -> Idris ()
ihPrintFunTypes h n []        = ihPrintError h $ "No such variable " ++ show n
ihPrintFunTypes h n overloads = do imp <- impShow
                                   ist <- getIState
                                   let output = vsep (map (uncurry (ppOverload imp)) overloads)
                                   case idris_outputmode ist of
                                     RawOutput -> consoleDisplayAnnotated h output
                                     IdeSlave n -> ideSlaveReturnAnnotated n h output
  where fullName n = annotate (AnnName n Nothing Nothing) $ text (show n)
        ppOverload imp n tm = fullName n <+> colon <+> align (prettyImp imp tm)

ihRenderResult :: Handle -> Doc OutputAnnotation -> Idris ()
ihRenderResult h d = do ist <- getIState
                        case idris_outputmode ist of
                          RawOutput -> consoleDisplayAnnotated h d
                          IdeSlave n -> ideSlaveReturnAnnotated n h d

fancifyAnnots :: IState -> OutputAnnotation -> OutputAnnotation
fancifyAnnots ist annot@(AnnName n _ _) =
  do let ctxt = tt_ctxt ist
     case () of
       _ | isDConName n ctxt -> AnnName n (Just DataOutput) Nothing
       _ | isFnName   n ctxt -> AnnName n (Just FunOutput) Nothing
       _ | isTConName n ctxt -> AnnName n (Just TypeOutput) Nothing
       _ | otherwise         -> annot
fancifyAnnots _ annot = annot

type1Doc :: Doc OutputAnnotation
type1Doc = (annotate AnnConstType $ text "Type 1")

ihPrintError :: Handle -> String -> Idris ()
ihPrintError h s = do i <- getIState
                      case idris_outputmode i of
                        RawOutput -> case s of
                                          "" -> return ()
                                          s  -> runIO $ hPutStrLn h s
                        IdeSlave n ->
                          let good = SexpList [SymbolAtom "error", toSExp s] in
                          runIO . hPutStrLn h $ convSExp "return" good n

ihputStrLn :: Handle -> String -> Idris ()
ihputStrLn h s = do i <- getIState
                    case idris_outputmode i of
                      RawOutput -> runIO $ hPutStrLn h s
                      IdeSlave n -> runIO . hPutStrLn h $ convSExp "write-string" s n

iputStrLn = ihputStrLn stdout
iPrintError = ihPrintError stdout
iPrintResult = ihPrintResult stdout
iWarn = ihWarn stdout

ideslavePutSExp :: SExpable a => String -> a -> Idris ()
ideslavePutSExp cmd info = do i <- getIState
                              case idris_outputmode i of
                                   IdeSlave n -> runIO . putStrLn $ convSExp cmd info n
                                   _ -> return ()

-- this needs some typing magic and more structured output towards emacs
iputGoal :: SimpleDoc OutputAnnotation -> Idris ()
iputGoal g = do i <- getIState
                case idris_outputmode i of
                  RawOutput -> runIO $ putStrLn (displayDecorated (consoleDecorate i) g)
                  IdeSlave n -> runIO . putStrLn $
                                convSExp "write-goal" (displayS (fmap (fancifyAnnots i) g) "") n

isetPrompt :: String -> Idris ()
isetPrompt p = do i <- getIState
                  case idris_outputmode i of
                    IdeSlave n -> runIO . putStrLn $ convSExp "set-prompt" p n

ihWarn :: Handle -> FC -> String -> Idris ()
ihWarn h fc err = do i <- getIState
                     case idris_outputmode i of
                       RawOutput -> runIO $ hPutStrLn h (show fc ++ ":" ++ err)
                       IdeSlave n -> runIO $ hPutStrLn h $ convSExp "warning" (fc_fname fc, fc_line fc, fc_column fc, err) n

setLogLevel :: Int -> Idris ()
setLogLevel l = do i <- getIState
                   let opts = idris_options i
                   let opt' = opts { opt_logLevel = l }
                   putIState $ i { idris_options = opt' }

setCmdLine :: [Opt] -> Idris ()
setCmdLine opts = do i <- getIState
                     let iopts = idris_options i
                     putIState $ i { idris_options = iopts { opt_cmdline = opts } }

getCmdLine :: Idris [Opt]
getCmdLine = do i <- getIState
                return (opt_cmdline (idris_options i))

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

setErrContext :: Bool -> Idris ()
setErrContext t = do i <- getIState
                     let opts = idris_options i
                     let opt' = opts { opt_errContext = t }
                     putIState $ i { idris_options = opt' }

errContext :: Idris Bool
errContext = do i <- getIState
                return (opt_errContext (idris_options i))

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

setNoBanner :: Bool -> Idris ()
setNoBanner n = do i <- getIState
                   let opts = idris_options i
                   let opt' = opts { opt_nobanner = n }
                   putIState $ i { idris_options = opt' }

getNoBanner :: Idris Bool
getNoBanner = do i <- getIState
                 let opts = idris_options i
                 return (opt_nobanner opts)

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

setIdeSlave :: Bool -> Idris ()
setIdeSlave True  = do i <- getIState
                       putIState $ i { idris_outputmode = (IdeSlave 0), idris_colourRepl = False }
setIdeSlave False = return ()

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

setOptLevel :: Word -> Idris ()
setOptLevel t = do i <- getIState
                   let opts = idris_options i
                       opt' = opts { opt_optLevel = t }
                   putIState $ i { idris_options = opt' }

optLevel :: Idris Word
optLevel = do i <- getIState
              return (opt_optLevel (idris_options i))

verbose :: Idris Bool
verbose = do i <- getIState
             return (opt_verbose (idris_options i))

setVerbose :: Bool -> Idris ()
setVerbose t = do i <- getIState
                  let opts = idris_options i
                  let opt' = opts { opt_verbose = t }
                  putIState $ i { idris_options = opt' }

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
                     let opt' = opts { opt_importdirs = fp : opt_importdirs opts }
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

colourise :: Idris Bool
colourise = do i <- getIState
               return $ idris_colourRepl i

setColourise :: Bool -> Idris ()
setColourise b = do i <- getIState
                    putIState $ i { idris_colourRepl = b }

setOutH :: Handle -> Idris ()
setOutH h = do i <- getIState
               putIState $ i { idris_outh = h }

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
    where setColour' KeywordColour  c t = t { keywordColour = c }
          setColour' BoundVarColour c t = t { boundVarColour = c }
          setColour' ImplicitColour c t = t { implicitColour = c }
          setColour' FunctionColour c t = t { functionColour = c }
          setColour' TypeColour     c t = t { typeColour = c }
          setColour' DataColour     c t = t { dataColour = c }
          setColour' PromptColour   c t = t { promptColour = c }

logLvl :: Int -> String -> Idris ()
logLvl l str = do i <- getIState
                  let lvl = opt_logLevel (idris_options i)
                  when (lvl >= l) $
                    case idris_outputmode i of
                      RawOutput -> do runIO $ putStrLn str
                      IdeSlave n ->
                        do let good = SexpList [IntegerAtom (toInteger l), toSExp str]
                           runIO $ putStrLn $ convSExp "log" good n

cmdOptType :: Opt -> Idris Bool
cmdOptType x = do i <- getIState
                  return $ x `elem` opt_cmdline (idris_options i)

iLOG :: String -> Idris ()
iLOG = logLvl 1

noErrors :: Idris Bool
noErrors = do i <- getIState
              case errLine i of
                Nothing -> return True
                _       -> return False

setTypeCase :: Bool -> Idris ()
setTypeCase t = do i <- getIState
                   let opts = idris_options i
                   let opt' = opts { opt_typecase = t }
                   putIState $ i { idris_options = opt' }


-- Dealing with parameters

expandParams :: (Name -> Name) -> [(Name, PTerm)] ->
                [Name] -> -- all names
                [Name] -> -- names with no declaration
                PTerm -> PTerm
expandParams dec ps ns infs tm = en tm
  where
    -- if we shadow a name (say in a lambda binding) that is used in a call to
    -- a lifted function, we need access to both names - once in the scope of the
    -- binding and once to call the lifted functions. So we'll explicitly shadow
    -- it. (Yes, it's a hack. The alternative would be to resolve names earlier
    -- but we didn't...)

    mkShadow (UN n) = MN 0 n
    mkShadow (MN i n) = MN (i+1) n
    mkShadow (NS x s) = NS (mkShadow x) s

    en (PLam n t s)
       | n `elem` (map fst ps ++ ns)
               = let n' = mkShadow n in
                     PLam n' (en t) (en (shadow n n' s))
       | otherwise = PLam n (en t) (en s)
    en (PPi p n t s)
       | n `elem` (map fst ps ++ ns)
               = let n' = mkShadow n in
                     PPi p n' (en t) (en (shadow n n' s))
       | otherwise = PPi p n (en t) (en s)
    en (PLet n ty v s)
       | n `elem` (map fst ps ++ ns)
               = let n' = mkShadow n in
                     PLet n' (en ty) (en v) (en (shadow n n' s))
       | otherwise = PLet n (en ty) (en v) (en s)
    -- FIXME: Should only do this in a type signature!
    en (PDPair f (PRef f' n) t r)
       | n `elem` (map fst ps ++ ns) && t /= Placeholder
           = let n' = mkShadow n in
                 PDPair f (PRef f' n') (en t) (en (shadow n n' r))
    en (PEq f l r) = PEq f (en l) (en r)
    en (PRewrite f l r g) = PRewrite f (en l) (en r) (fmap en g)
    en (PTyped l r) = PTyped (en l) (en r)
    en (PPair f p l r) = PPair f p (en l) (en r)
    en (PDPair f l t r) = PDPair f (en l) (en t) (en r)
    en (PAlternative a as) = PAlternative a (map en as)
    en (PHidden t) = PHidden (en t)
    en (PUnifyLog t) = PUnifyLog (en t)
    en (PNoImplicits t) = PNoImplicits (en t)
    en (PDoBlock ds) = PDoBlock (map (fmap en) ds)
    en (PProof ts)   = PProof (map (fmap en) ts)
    en (PTactics ts) = PTactics (map (fmap en) ts)

    en (PQuote (Var n))
        | n `nselem` ns = PQuote (Var (dec n))
    en (PApp fc (PInferRef fc' n) as)
        | n `nselem` ns = PApp fc (PInferRef fc' (dec n))
                           (map (pexp . (PRef fc)) (map fst ps) ++ (map (fmap en) as))
    en (PApp fc (PRef fc' n) as)
        | n `elem` infs = PApp fc (PInferRef fc' (dec n))
                           (map (pexp . (PRef fc)) (map fst ps) ++ (map (fmap en) as))
        | n `nselem` ns = PApp fc (PRef fc' (dec n))
                           (map (pexp . (PRef fc)) (map fst ps) ++ (map (fmap en) as))
    en (PAppBind fc (PRef fc' n) as)
        | n `elem` infs = PAppBind fc (PInferRef fc' (dec n))
                           (map (pexp . (PRef fc)) (map fst ps) ++ (map (fmap en) as))
        | n `nselem` ns = PAppBind fc (PRef fc' (dec n))
                           (map (pexp . (PRef fc)) (map fst ps) ++ (map (fmap en) as))
    en (PRef fc n)
        | n `elem` infs = PApp fc (PInferRef fc (dec n))
                           (map (pexp . (PRef fc)) (map fst ps))
        | n `nselem` ns = PApp fc (PRef fc (dec n))
                           (map (pexp . (PRef fc)) (map fst ps))
    en (PInferRef fc n)
        | n `nselem` ns = PApp fc (PInferRef fc (dec n))
                           (map (pexp . (PRef fc)) (map fst ps))
    en (PApp fc f as) = PApp fc (en f) (map (fmap en) as)
    en (PAppBind fc f as) = PAppBind fc (en f) (map (fmap en) as)
    en (PCase fc c os) = PCase fc (en c) (map (pmap en) os)
    en t = t

    nselem x [] = False
    nselem x (y : xs) | nseq x y = True
                      | otherwise = nselem x xs

    nseq x y = nsroot x == nsroot y

expandParamsD :: Bool -> -- True = RHS only
                 IState ->
                 (Name -> Name) -> [(Name, PTerm)] -> [Name] -> PDecl -> PDecl
expandParamsD rhsonly ist dec ps ns (PTy doc syn fc o n ty)
    = if n `elem` ns && (not rhsonly)
         then -- trace (show (n, expandParams dec ps ns ty)) $
              PTy doc syn fc o (dec n) (piBindp expl_param ps (expandParams dec ps ns [] ty))
         else --trace (show (n, expandParams dec ps ns ty)) $
              PTy doc syn fc o n (expandParams dec ps ns [] ty)
expandParamsD rhsonly ist dec ps ns (PPostulate doc syn fc o n ty)
    = if n `elem` ns && (not rhsonly)
         then -- trace (show (n, expandParams dec ps ns ty)) $
              PPostulate doc syn fc o (dec n) (piBind ps
                            (expandParams dec ps ns [] ty))
         else --trace (show (n, expandParams dec ps ns ty)) $
              PPostulate doc syn fc o n (expandParams dec ps ns [] ty)
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
    expandParamsC (PWith fc n lhs ws wval ds)
        = let -- ps' = updateps True (namesIn ist wval) (zip ps [0..])
              ps'' = updateps False (namesIn [] ist lhs) (zip ps [0..])
              lhs' = if rhsonly then lhs else (expandParams dec ps'' ns [] lhs)
              n' = if n `elem` ns then dec n else n
              ns' = removeBound lhs ns in
              PWith fc n' lhs'
                          (map (expandParams dec ps'' ns' []) ws)
                          (expandParams dec ps'' ns' [] wval)
                          (map (expandParamsD rhsonly ist dec ps'' ns') ds)
    updateps yn nm [] = []
    updateps yn nm (((a, t), i):as)
        | (a `elem` nm) == yn = (a, t) : updateps yn nm as
        | otherwise = (sMN i (show n ++ "_u"), t) : updateps yn nm as

    removeBound lhs ns = ns \\ nub (bnames lhs)

    bnames (PRef _ n) = [n]
    bnames (PApp _ _ args) = concatMap bnames (map getTm args)
    bnames (PPair _ _ l r) = bnames l ++ bnames r
    bnames (PDPair _ l Placeholder r) = bnames l ++ bnames r
    bnames _ = []

expandParamsD rhs ist dec ps ns (PData doc syn fc co pd)
    = PData doc syn fc co (expandPData pd)
  where
    -- just do the type decl, leave constructors alone (parameters will be
    -- added implicitly)
    expandPData (PDatadecl n ty cons)
       = if n `elem` ns
            then PDatadecl (dec n) (piBind ps (expandParams dec ps ns [] ty))
                           (map econ cons)
            else PDatadecl n (expandParams dec ps ns [] ty) (map econ cons)
    econ (doc, n, t, fc, fs)
       = (doc, dec n, piBindp expl ps (expandParams dec ps ns [] t), fc, fs)
expandParamsD rhs ist dec ps ns (PParams f params pds)
   = PParams f (ps ++ map (mapsnd (expandParams dec ps ns [])) params)
               (map (expandParamsD True ist dec ps ns) pds)
--                (map (expandParamsD ist dec ps ns) pds)
expandParamsD rhs ist dec ps ns (PMutual f pds)
   = PMutual f (map (expandParamsD rhs ist dec ps ns) pds)
expandParamsD rhs ist dec ps ns (PClass doc info f cs n params decls)
   = PClass doc info f
           (map (expandParams dec ps ns []) cs)
           n
           (map (mapsnd (expandParams dec ps ns [])) params)
           (map (expandParamsD rhs ist dec ps ns) decls)
expandParamsD rhs ist dec ps ns (PInstance info f cs n params ty cn decls)
   = PInstance info f
           (map (expandParams dec ps ns []) cs)
           n
           (map (expandParams dec ps ns []) params)
           (expandParams dec ps ns [] ty)
           cn
           (map (expandParamsD rhs ist dec ps ns) decls)
expandParamsD rhs ist dec ps ns d = d

mapsnd f (x, t) = (x, f t)

-- Calculate a priority for a type, for deciding elaboration order
-- * if it's just a type variable or concrete type, do it early (0)
-- * if there's only type variables and injective constructors, do it next (1)
-- * if there's a function type, next (2)
-- * finally, everything else (3)

getPriority :: IState -> PTerm -> Int
getPriority i tm = 1 -- pri tm
  where
    pri (PRef _ n) =
        case lookupP n (tt_ctxt i) of
            ((P (DCon _ _) _ _):_) -> 1
            ((P (TCon _ _) _ _):_) -> 1
            ((P Ref _ _):_) -> 1
            [] -> 0 -- must be locally bound, if it's not an error...
    pri (PPi _ _ x y) = max 5 (max (pri x) (pri y))
    pri (PTrue _ _) = 0
    pri (PFalse _) = 0
    pri (PRefl _ _) = 1
    pri (PEq _ l r) = max 1 (max (pri l) (pri r))
    pri (PRewrite _ l r _) = max 1 (max (pri l) (pri r))
    pri (PApp _ f as) = max 1 (max (pri f) (foldr max 0 (map (pri.getTm) as)))
    pri (PAppBind _ f as) = max 1 (max (pri f) (foldr max 0 (map (pri.getTm) as)))
    pri (PCase _ f as) = max 1 (max (pri f) (foldr max 0 (map (pri.snd) as)))
    pri (PTyped l r) = pri l
    pri (PPair _ _ l r) = max 1 (max (pri l) (pri r))
    pri (PDPair _ l t r) = max 1 (max (pri l) (max (pri t) (pri r)))
    pri (PAlternative a as) = maximum (map pri as)
    pri (PConstant _) = 0
    pri Placeholder = 1
    pri _ = 3

addStatics :: Name -> Term -> PTerm -> Idris ()
addStatics n tm ptm =
    do let (statics, dynamics) = initStatics tm ptm
       let stnames = nub $ concatMap freeArgNames (map snd statics)
       let dnames = nub $ concatMap freeArgNames (map snd dynamics)
       -- also get the arguments which are 'uniquely inferrable' from
       -- statics (see sec 4.2 of "Scrapping Your Inefficient Engine")
       let statics' = nub $ map fst statics ++
                              filter (\x -> not (elem x dnames)) stnames
       let stpos = staticList statics' tm
       i <- getIState
       when (not (null statics)) $
          logLvl 5 $ show n ++ " " ++ show statics' ++ "\n" ++ show dynamics
                        ++ "\n" ++ show stnames ++ "\n" ++ show dnames
       putIState $ i { idris_statics = addDef n stpos (idris_statics i) }
       addIBC (IBCStatic n)
  where
    initStatics (Bind n (Pi ty) sc) (PPi p _ _ s)
            = let (static, dynamic) = initStatics (instantiate (P Bound n ty) sc) s in
                  if pstatic p == Static then ((n, ty) : static, dynamic)
                    else if (not (searchArg p)) 
                            then (static, (n, ty) : dynamic)
                            else (static, dynamic)
    initStatics t pt = ([], [])

    freeArgNames (Bind n (Pi ty) sc) 
          = nub $ freeArgNames ty 
    freeArgNames tm = let (_, args) = unApply tm in
                          concatMap freeNames args

    -- if a name appears in a type class or tactic implicit index, it doesn't
    -- affect its 'uniquely inferrable' from a static status since these are
    -- resolved by searching.
    searchArg (Constraint _ _ _) = True
    searchArg (TacImp _ _ _ _) = True
    searchArg _ = False

    staticList sts (Bind n (Pi _) sc) = (n `elem` sts) : staticList sts sc
    staticList _ _ = []

-- Dealing with implicit arguments

-- Add constraint bindings from using block

addUsingConstraints :: SyntaxInfo -> FC -> PTerm -> Idris PTerm
addUsingConstraints syn fc t
   = do ist <- get
        let ns = namesIn [] ist t
        let cs = getConstraints t -- check declared constraints
        let addconsts = uconsts \\ cs
        -- if all names in the arguments of addconsts appear in ns,
        -- add the constraint implicitly
        return (doAdd addconsts ns t)
   where uconsts = filter uconst (using syn)
         uconst (UConstraint _ _) = True
         uconst _ = False

         doAdd [] _ t = t
         -- if all of args in ns, then add it
         doAdd (UConstraint c args : cs) ns t
             | all (\n -> elem n ns) args
                   = PPi (Constraint [] Dynamic "") (sMN 0 "cu")
                         (mkConst c args) (doAdd cs ns t)
             | otherwise = doAdd cs ns t

         mkConst c args = PApp fc (PRef fc c)
                             (map (\n -> PExp 0 [] (PRef fc n) "") args)

         getConstraints (PPi (Constraint _ _ _) _ c sc)
             = getcapp c ++ getConstraints sc
         getConstraints (PPi _ _ c sc) = getConstraints sc
         getConstraints _ = []

         getcapp (PApp _ (PRef _ c) args)
             = do ns <- mapM getName args
                  return (UConstraint c ns)
         getcapp _ = []

         getName (PExp _ _ (PRef _ n) _) = return n
         getName _ = []

-- Add implicit Pi bindings for any names in the term which appear in an
-- argument position.

-- This has become a right mess already. Better redo it some time...

implicit :: SyntaxInfo -> Name -> PTerm -> Idris PTerm
implicit syn n ptm = implicit' syn [] n ptm

implicit' :: SyntaxInfo -> [Name] -> Name -> PTerm -> Idris PTerm
implicit' syn ignore n ptm
    = do i <- getIState
         let (tm', impdata) = implicitise syn ignore i ptm
--          let (tm'', spos) = findStatics i tm'
         putIState $ i { idris_implicits = addDef n impdata (idris_implicits i) }
         addIBC (IBCImp n)
         logLvl 5 ("Implicit " ++ show n ++ " " ++ show impdata)
--          i <- get
--          putIState $ i { idris_statics = addDef n spos (idris_statics i) }
         return tm'

implicitise :: SyntaxInfo -> [Name] -> IState -> PTerm -> (PTerm, [PArg])
implicitise syn ignore ist tm = -- trace ("INCOMING " ++ showImp True tm) $
      let (declimps, ns') = execState (imps True [] tm) ([], [])
          ns = filter (\n -> implicitable n || elem n (map fst uvars)) $
                  ns' \\ (map fst pvars ++ no_imp syn ++ ignore)
          nsOrder = filter (not . inUsing) ns ++ filter inUsing ns in
          if null ns
            then (tm, reverse declimps)
            else implicitise syn ignore ist (pibind uvars nsOrder tm)
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

    imps top env (PApp _ f as)
       = do (decls, ns) <- get
            let isn = concatMap (namesIn uvars ist) (map getTm as)
            put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PPi (Imp l _ doc _) n ty sc)
        = do let isn = nub (namesIn uvars ist ty) `dropAll` [n]
             (decls , ns) <- get
             put (PImp (getPriority ist ty) True l n Placeholder doc : decls,
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (Exp l _ doc _) n ty sc)
        = do let isn = nub (namesIn uvars ist ty ++ case sc of
                            (PRef _ x) -> namesIn uvars ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PExp (getPriority ist ty) l Placeholder doc : decls,
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (Constraint l _ doc) n ty sc)
        = do let isn = nub (namesIn uvars ist ty ++ case sc of
                            (PRef _ x) -> namesIn uvars ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PConstraint 10 l Placeholder doc : decls,
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (TacImp l _ scr doc) n ty sc)
        = do let isn = nub (namesIn uvars ist ty ++ case sc of
                            (PRef _ x) -> namesIn uvars ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PTacImplicit 10 l n scr Placeholder doc : decls,
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PEq _ l r)
        = do (decls, ns) <- get
             let isn = namesIn uvars ist l ++ namesIn uvars ist r
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PRewrite _ l r _)
        = do (decls, ns) <- get
             let isn = namesIn uvars ist l ++ namesIn uvars ist r
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PTyped l r)
        = imps top env l
    imps top env (PPair _ _ l r)
        = do (decls, ns) <- get
             let isn = namesIn uvars ist l ++ namesIn uvars ist r
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PDPair _ (PRef _ n) t r)
        = do (decls, ns) <- get
             let isn = nub (namesIn uvars ist t ++ namesIn uvars ist r) \\ [n]
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PDPair _ l t r)
        = do (decls, ns) <- get
             let isn = namesIn uvars ist l ++ namesIn uvars ist t ++
                       namesIn uvars ist r
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PAlternative a as)
        = do (decls, ns) <- get
             let isn = concatMap (namesIn uvars ist) as
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PLam n ty sc)
        = do imps False env ty
             imps False (n:env) sc
    imps top env (PHidden tm)    = imps False env tm
    imps top env (PUnifyLog tm)  = imps False env tm
    imps top env (PNoImplicits tm)  = imps False env tm
    imps top env _               = return ()

    pibind using []     sc = sc
    pibind using (n:ns) sc
      = case lookup n using of
            Just ty -> PPi (Imp [] Dynamic "" False) n ty (pibind using ns sc)
            Nothing -> PPi (Imp [] Dynamic "" False) n Placeholder
                                   (pibind using ns sc)

-- Add implicit arguments in function calls
addImplPat :: IState -> PTerm -> PTerm
addImplPat = addImpl' True [] []

addImplBound :: IState -> [Name] -> PTerm -> PTerm
addImplBound ist ns = addImpl' False ns [] ist

addImplBoundInf :: IState -> [Name] -> [Name] -> PTerm -> PTerm
addImplBoundInf ist ns inf = addImpl' False ns inf ist

addImpl :: IState -> PTerm -> PTerm
addImpl = addImpl' False [] []

-- TODO: in patterns, don't add implicits to function names guarded by constructors
-- and *not* inside a PHidden

addImpl' :: Bool -> [Name] -> [Name] -> IState -> PTerm -> PTerm
addImpl' inpat env infns ist ptm 
         = mkUniqueNames env (ai (zip env (repeat Nothing)) [] ptm)
  where
    ai env ds (PRef fc f)
        | f `elem` infns = PInferRef fc f
        | not (f `elem` map fst env) = handleErr $ aiFn inpat inpat ist fc f ds []
    ai env ds (PHidden (PRef fc f))
        | not (f `elem` map fst env) = handleErr $ aiFn inpat False ist fc f ds []
    ai env ds (PEq fc l r)   
      = let l' = ai env ds l
            r' = ai env ds r in
            PEq fc l' r'
    ai env ds (PRewrite fc l r g)   
       = let l' = ai env ds l
             r' = ai env ds r
             g' = fmap (ai env ds) g in
         PRewrite fc l' r' g'
    ai env ds (PTyped l r) 
      = let l' = ai env ds l
            r' = ai env ds r in
            PTyped l' r'
    ai env ds (PPair fc p l r) 
      = let l' = ai env ds l
            r' = ai env ds r in
            PPair fc p l' r'
    ai env ds (PDPair fc l t r)
         = let l' = ai env ds l
               t' = ai env ds t
               r' = ai env ds r in
           PDPair fc l' t' r'
    ai env ds (PAlternative a as) 
           = let as' = map (ai env ds) as in
                 PAlternative a as'
    ai env _ (PDisamb ds' as) = ai env ds' as
    ai env ds (PApp fc (PInferRef _ f) as)
        = let as' = map (fmap (ai env ds)) as in
              PApp fc (PInferRef fc f) as'
    ai env ds (PApp fc ftm@(PRef _ f) as)
        | f `elem` infns = ai env ds (PApp fc (PInferRef fc f) as)
        | not (f `elem` map fst env)
                          = let as' = map (fmap (ai env ds)) as in
                                handleErr $ aiFn inpat False ist fc f ds as'
        | Just (Just ty) <- lookup f env =
             let as' = map (fmap (ai env ds)) as
                 arity = getPArity ty in
              mkPApp fc arity ftm as'
    ai env ds (PApp fc f as) 
      = let f' = ai env ds f
            as' = map (fmap (ai env ds)) as in
         mkPApp fc 1 f' as'
    ai env ds (PCase fc c os) 
      = let c' = ai env ds c
            os' = map (pmap (ai env ds)) os in
            PCase fc c' os'
    ai env ds (PLam n ty sc) 
      = let ty' = ai env ds ty
            sc' = ai ((n, Just ty):env) ds sc in
            PLam n ty' sc'
    ai env ds (PLet n ty val sc)
      = let ty' = ai env ds ty
            val' = ai env ds val
            sc' = ai ((n, Just ty):env) ds sc in
            PLet n ty' val' sc'
    ai env ds (PPi p n ty sc) 
      = let ty' = ai env ds ty
            sc' = ai ((n, Just ty):env) ds sc in
            PPi p n ty' sc'
    ai env ds (PGoal fc r n sc) 
      = let r' = ai env ds r
            sc' = ai ((n, Nothing):env) ds sc in
            PGoal fc r' n sc'
    ai env ds (PHidden tm) = PHidden (ai env ds tm)
    ai env ds (PProof ts) = PProof (map (fmap (ai env ds)) ts)
    ai env ds (PTactics ts) = PTactics (map (fmap (ai env ds)) ts)
    ai env ds (PRefl fc tm) = PRefl fc (ai env ds tm)
    ai env ds (PUnifyLog tm) = PUnifyLog (ai env ds tm)
    ai env ds (PNoImplicits tm) = PNoImplicits (ai env ds tm)
    ai env ds tm = tm

    handleErr (Left err) = PElabError err
    handleErr (Right x) = x

-- if in a pattern, and there are no arguments, and there's no possible
-- names with zero explicit arguments, don't add implicits.

aiFn :: Bool -> Bool -> IState -> FC -> Name -> [[T.Text]] -> [PArg] -> Either Err PTerm
aiFn inpat True ist fc f ds []
  = case lookupDef f (tt_ctxt ist) of
        [] -> Right $ PPatvar fc f
        alts -> let ialts = lookupCtxtName f (idris_implicits ist) in
                    -- trace (show f ++ " " ++ show (fc, any (all imp) ialts, ialts, any constructor alts)) $
                    if (not (vname f) || tcname f
                           || any (conCaf (tt_ctxt ist)) ialts)
--                            any constructor alts || any allImp ialts))
                        then aiFn inpat False ist fc f ds [] -- use it as a constructor
                        else Right $ PPatvar fc f
    where imp (PExp _ _ _ _) = False
          imp _ = True
--           allImp [] = False
          allImp xs = all imp xs
          constructor (TyDecl (DCon _ _) _) = True
          constructor _ = False

          conCaf ctxt (n, cia) = isDConName n ctxt && allImp cia

          vname (UN n) = True -- non qualified
          vname _ = False

aiFn inpat expat ist fc f ds as
    | f `elem` primNames = Right $ PApp fc (PRef fc f) as
aiFn inpat expat ist fc f ds as
          -- This is where namespaces get resolved by adding PAlternative
     = do let ns = lookupCtxtName f (idris_implicits ist)
          let nh = filter (\(n, _) -> notHidden n) ns
          let ns' = case trimAlts ds nh of
                         [] -> nh
                         x -> x 
          case ns' of
            [(f',ns)] -> Right $ mkPApp fc (length ns) (PRef fc f') (insertImpl ns as)
            [] -> if f `elem` (map fst (idris_metavars ist))
                    then Right $ PApp fc (PRef fc f) as
                    else Right $ mkPApp fc (length as) (PRef fc f) as
            alts -> Right $
                         PAlternative True $
                           map (\(f', ns) -> mkPApp fc (length ns) (PRef fc f')
                                                  (insertImpl ns as)) alts
  where
    trimAlts [] alts = alts
    trimAlts ns alts 
        = filter (\(x, _) -> any (\d -> d `isPrefixOf` nspace x) ns) alts

    nspace (NS _ s) = s
    nspace _ = []

    notHidden n = case getAccessibility n of
                        Hidden -> False
                        _ -> True

    getAccessibility n
             = case lookupDefAcc n False (tt_ctxt ist) of
                    [(n,t)] -> t
                    _ -> Public


    insertImpl :: [PArg] -> [PArg] -> [PArg]
    insertImpl (PExp p l ty _ : ps) (PExp _ _ tm d : given) =
                                 PExp p l tm d : insertImpl ps given
    insertImpl (PConstraint p l ty _ : ps) (PConstraint _ _ tm d : given) =
                                 PConstraint p l tm d : insertImpl ps given
    insertImpl (PConstraint p l ty d : ps) given =
                 PConstraint p l (PResolveTC fc) d : insertImpl ps given
    insertImpl (PImp p _ l n ty d : ps) given =
        case find n given [] of
            Just (tm, given') -> PImp p False l n tm "" : insertImpl ps given'
            Nothing ->           PImp p True l n Placeholder "" : insertImpl ps given
    insertImpl (PTacImplicit p l n sc' ty d : ps) given =
      let sc = addImpl ist sc' in
        case find n given [] of
            Just (tm, given') -> PTacImplicit p l n sc tm "" : insertImpl ps given'
            Nothing -> if inpat
                          then PTacImplicit p l n sc Placeholder "" : insertImpl ps given
                          else PTacImplicit p l n sc sc "" : insertImpl ps given
    insertImpl expected [] = []
    insertImpl _        given  = given

    find n []               acc = Nothing
    find n (PImp _ _ _ n' t _ : gs) acc
         | n == n' = Just (t, reverse acc ++ gs)
    find n (PTacImplicit _ _ n' _ t _ : gs) acc
         | n == n' = Just (t, reverse acc ++ gs)
    find n (g : gs) acc = find n gs (g : acc)

-- replace non-linear occurrences with _
-- ASSUMPTION: This is called before adding 'alternatives' because otherwise
-- it is hard to get right!

stripLinear :: IState -> PTerm -> PTerm
stripLinear i tm = evalState (sl tm) [] where
    sl :: PTerm -> State [Name] PTerm
    sl (PRef fc f)
         | (_:_) <- lookupTy f (tt_ctxt i)
              = return $ PRef fc f
         | otherwise = do ns <- get
                          if (f `elem` ns)
                             then return Placeholder
                             else do put (f : ns)
                                     return (PRef fc f)
    sl (PPatvar fc f)
                     = do ns <- get
                          if (f `elem` ns)
                             then return Placeholder
                             else do put (f : ns)
                                     return (PPatvar fc f)
    sl (PApp fc fn args) = do fn' <- sl fn
                              args' <- mapM slA args
                              return $ PApp fc fn' args'
       where slA (PImp p m l n t d) = do t' <- sl t
                                         return $ PImp p m l n t' d
             slA (PExp p l t d) = do t' <- sl t
                                     return $ PExp p l t' d
             slA (PConstraint p l t d)
                                = do t' <- sl t
                                     return $ PConstraint p l t' d
             slA (PTacImplicit p l n sc t d)
                                = do t' <- sl t
                                     return $ PTacImplicit p l n sc t' d
    sl x = return x

-- Remove functions which aren't applied to anything, which must then
-- be resolved by unification. Assume names resolved and alternatives
-- filled in (so no ambiguity).

stripUnmatchable :: IState -> PTerm -> PTerm
stripUnmatchable i (PApp fc fn args) = PApp fc fn (fmap (fmap su) args) where
    su :: PTerm -> PTerm
    su (PRef fc f)
       | (Bind n (Pi t) sc :_) <- lookupTy f (tt_ctxt i) 
          = Placeholder
    su (PApp fc fn args) 
       = PApp fc fn (fmap (fmap su) args)
    su (PAlternative b alts) 
       = let alts' = filter (/= Placeholder) (map su alts) in
             if null alts' then Placeholder
                           else PAlternative b alts'
    su (PPair fc p l r) = PPair fc p (su l) (su r)
    su (PDPair fc l t r) = PDPair fc (su l) (su t) (su r)
    su t = t
stripUnmatchable i tm = tm

mkPApp fc a f [] = f
mkPApp fc a f as = let rest = drop a as in
                       appRest fc (PApp fc f (take a as)) rest
  where
    appRest fc f [] = f
    appRest fc f (a : as) = appRest fc (PApp fc f [a]) as

-- Find 'static' argument positions
-- (the declared ones, plus any names in argument position in the declared
-- statics)
-- FIXME: It's possible that this really has to happen after elaboration

findStatics :: IState -> PTerm -> (PTerm, [Bool])
findStatics ist tm = trace (show tm) $
                      let (ns, ss) = fs tm in
                         runState (pos ns ss tm) []
  where fs (PPi p n t sc)
            | Static <- pstatic p
                        = let (ns, ss) = fs sc in
                              (namesIn [] ist t : ns, n : ss)
            | otherwise = let (ns, ss) = fs sc in
                              (ns, ss)
        fs _ = ([], [])

        inOne n ns = length (filter id (map (elem n) ns)) == 1

        pos ns ss (PPi p n t sc)
            | elem n ss = do sc' <- pos ns ss sc
                             spos <- get
                             put (True : spos)
                             return (PPi (p { pstatic = Static }) n t sc')
            | otherwise = do sc' <- pos ns ss sc
                             spos <- get
                             put (False : spos)
                             return (PPi p n t sc')
        pos ns ss t = return t

-- for 6.12/7 compatibility
data EitherErr a b = LeftErr a | RightOK b

instance Monad (EitherErr a) where
    return = RightOK

    (LeftErr e) >>= k = LeftErr e
    RightOK v   >>= k = k v

toEither (LeftErr e)  = Left e
toEither (RightOK ho) = Right ho

-- syntactic match of a against b, returning pair of variables in a
-- and what they match. Returns the pair that failed if not a match.

matchClause :: IState -> PTerm -> PTerm -> Either (PTerm, PTerm) [(Name, PTerm)]
matchClause = matchClause' False

matchClause' :: Bool -> IState -> PTerm -> PTerm -> Either (PTerm, PTerm) [(Name, PTerm)]
matchClause' names i x y = checkRpts $ match (fullApp x) (fullApp y) where
    matchArg x y = match (fullApp (getTm x)) (fullApp (getTm y))

    fullApp (PApp _ (PApp fc f args) xs) = fullApp (PApp fc f (args ++ xs))
    fullApp x = x

    match' x y = match (fullApp x) (fullApp y)
    match (PApp _ (PRef _ (NS (UN fi) [b])) [_,_,x]) x'
        | fi == txt "fromInteger" && b == txt "builtins",
          PConstant (I _) <- getTm x = match (getTm x) x'
    match x' (PApp _ (PRef _ (NS (UN fi) [b])) [_,_,x])
        | fi == txt "fromInteger" && b == txt "builtins",
          PConstant (I _) <- getTm x = match (getTm x) x'
    match (PApp _ (PRef _ (UN l)) [_,x]) x' | l == txt "lazy" = match (getTm x) x'
    match x (PApp _ (PRef _ (UN l)) [_,x']) | l == txt "lazy" = match x (getTm x')
    match (PApp _ f args) (PApp _ f' args')
        | length args == length args'
            = do mf <- match' f f'
                 ms <- zipWithM matchArg args args'
                 return (mf ++ concat ms)
--     match (PRef _ n) (PRef _ n') | n == n' = return []
--                                  | otherwise = Nothing
    match (PRef f n) (PApp _ x []) = match (PRef f n) x
    match (PPatvar f n) xr = match (PRef f n) xr
    match xr (PPatvar f n) = match xr (PRef f n)
    match (PApp _ x []) (PRef f n) = match x (PRef f n)
    match (PRef _ n) tm@(PRef _ n')
        | n == n' && not names &&
          (not (isConName n (tt_ctxt i) || isFnName n (tt_ctxt i)) 
                || tm == Placeholder)
            = return [(n, tm)]
        | n == n' = return []
    match (PRef _ n) tm
        | not names && (not (isConName n (tt_ctxt i) ||
                             isFnName n (tt_ctxt i)) || tm == Placeholder)
            = return [(n, tm)]
    match (PEq _ l r) (PEq _ l' r') = do ml <- match' l l'
                                         mr <- match' r r'
                                         return (ml ++ mr)
    match (PRewrite _ l r _) (PRewrite _ l' r' _)
                                    = do ml <- match' l l'
                                         mr <- match' r r'
                                         return (ml ++ mr)
    match (PTyped l r) (PTyped l' r') = do ml <- match l l'
                                           mr <- match r r'
                                           return (ml ++ mr)
    match (PTyped l r) x = match l x
    match x (PTyped l r) = match x l
    match (PPair _ _ l r) (PPair _ _ l' r') = do ml <- match' l l'
                                                 mr <- match' r r'
                                                 return (ml ++ mr)
    match (PDPair _ l t r) (PDPair _ l' t' r') = do ml <- match' l l'
                                                    mt <- match' t t'
                                                    mr <- match' r r'
                                                    return (ml ++ mt ++ mr)
    match (PAlternative a as) (PAlternative a' as')
        = do ms <- zipWithM match' as as'
             return (concat ms)
    match a@(PAlternative _ as) b
        = do let ms = zipWith match' as (repeat b)
             case (rights (map toEither ms)) of
                (x: _) -> return x
                _ -> LeftErr (a, b)
    match (PCase _ _ _) _ = return [] -- lifted out
    match (PMetavar _) _ = return [] -- modified
    match (PInferRef _ _) _ = return [] -- modified
    match (PQuote _) _ = return []
    match (PProof _) _ = return []
    match (PTactics _) _ = return []
    match (PRefl _ _) (PRefl _ _) = return []
    match (PResolveTC _) (PResolveTC _) = return []
    match (PTrue _ _) (PTrue _ _) = return []
    match (PFalse _) (PFalse _) = return []
    match (PReturn _) (PReturn _) = return []
    match (PPi _ _ t s) (PPi _ _ t' s') = do mt <- match' t t'
                                             ms <- match' s s'
                                             return (mt ++ ms)
    match (PLam _ t s) (PLam _ t' s') = do mt <- match' t t'
                                           ms <- match' s s'
                                           return (mt ++ ms)
    match (PLet _ t ty s) (PLet _ t' ty' s') = do mt <- match' t t'
                                                  mty <- match' ty ty'
                                                  ms <- match' s s'
                                                  return (mt ++ mty ++ ms)
    match (PHidden x) (PHidden y) = match' x y
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

substMatchesShadow :: [(Name, PTerm)] -> [Name] -> PTerm -> PTerm
substMatchesShadow [] shs t = t
substMatchesShadow ((n,tm):ns) shs t
   = substMatchShadow n shs tm (substMatchesShadow ns shs t)

substMatch :: Name -> PTerm -> PTerm -> PTerm
substMatch n = substMatchShadow n []

substMatchShadow :: Name -> [Name] -> PTerm -> PTerm -> PTerm
substMatchShadow n shs tm t = sm shs t where
    sm xs (PRef _ n') | n == n' = tm
    sm xs (PLam x t sc) = PLam x (sm xs t) (sm xs sc)
    sm xs (PPi p x t sc)
         | x `elem` xs
             = let x' = nextName x in
                   PPi p x' (sm (x':xs) (substMatch x (PRef emptyFC x') t))
                            (sm (x':xs) (substMatch x (PRef emptyFC x') sc))
         | otherwise = PPi p x (sm xs t) (sm (x : xs) sc)
    sm xs (PApp f x as) = fullApp $ PApp f (sm xs x) (map (fmap (sm xs)) as)
    sm xs (PCase f x as) = PCase f (sm xs x) (map (pmap (sm xs)) as)
    sm xs (PEq f x y) = PEq f (sm xs x) (sm xs y)
    sm xs (PRewrite f x y tm) = PRewrite f (sm xs x) (sm xs y)
                                           (fmap (sm xs) tm)
    sm xs (PTyped x y) = PTyped (sm xs x) (sm xs y)
    sm xs (PPair f p x y) = PPair f p (sm xs x) (sm xs y)
    sm xs (PDPair f x t y) = PDPair f (sm xs x) (sm xs t) (sm xs y)
    sm xs (PAlternative a as) = PAlternative a (map (sm xs) as)
    sm xs (PHidden x) = PHidden (sm xs x)
    sm xs (PUnifyLog x) = PUnifyLog (sm xs x)
    sm xs (PNoImplicits x) = PNoImplicits (sm xs x)
    sm xs x = x

    fullApp (PApp _ (PApp fc f args) xs) = fullApp (PApp fc f (args ++ xs))
    fullApp x = x

shadow :: Name -> Name -> PTerm -> PTerm
shadow n n' t = sm t where
    sm (PRef fc x) | n == x = PRef fc n'
    sm (PLam x t sc) | n /= x = PLam x (sm t) (sm sc)
    sm (PPi p x t sc) | n /=x = PPi p x (sm t) (sm sc)
    sm (PLet x t v sc) | n /= x = PLet x (sm t) (sm v) (sm sc)
    sm (PApp f x as) = PApp f (sm x) (map (fmap sm) as)
    sm (PAppBind f x as) = PAppBind f (sm x) (map (fmap sm) as)
    sm (PCase f x as) = PCase f (sm x) (map (pmap sm) as)
    sm (PEq f x y) = PEq f (sm x) (sm y)
    sm (PRewrite f x y tm) = PRewrite f (sm x) (sm y) (fmap sm tm)
    sm (PTyped x y) = PTyped (sm x) (sm y)
    sm (PPair f p x y) = PPair f p (sm x) (sm y)
    sm (PDPair f x t y) = PDPair f (sm x) (sm t) (sm y)
    sm (PAlternative a as) = PAlternative a (map sm as)
    sm (PTactics ts) = PTactics (map (fmap sm) ts)
    sm (PProof ts) = PProof (map (fmap sm) ts)
    sm (PHidden x) = PHidden (sm x)
    sm (PUnifyLog x) = PUnifyLog (sm x)
    sm (PNoImplicits x) = PNoImplicits (sm x)
    sm x = x

-- Rename any binders which are repeated (so that we don't have to mess
-- about with shadowing anywhere else).

mkUniqueNames :: [Name] -> PTerm -> PTerm
mkUniqueNames env tm = evalState (mkUniq tm) env where
  inScope = boundNamesIn tm

  mkUniqA arg = do t' <- mkUniq (getTm arg)
                   return (arg { getTm = t' })

  -- FIXME: Probably ought to do this for completeness! It's fine as
  -- long as there are no bindings inside tactics though.
  mkUniqT tac = return tac

  mkUniq :: PTerm -> State [Name] PTerm
  mkUniq (PLam n ty sc)
         = do env <- get
              (n', sc') <-
                    if n `elem` env
                       then do let n' = uniqueName n (env ++ inScope)
                               return (n', shadow n n' sc)
                       else return (n, sc)
              put (n' : env)
              ty' <- mkUniq ty
              sc'' <- mkUniq sc'
              return $! PLam n' ty' sc''
  mkUniq (PPi p n ty sc)
         = do env <- get
              (n', sc') <-
                    if n `elem` env
                       then do let n' = uniqueName n (env ++ inScope)
                               return (n', shadow n n' sc)
                       else return (n, sc)
              put (n' : env)
              ty' <- mkUniq ty
              sc'' <- mkUniq sc'
              return $! PPi p n' ty' sc''
  mkUniq (PLet n ty val sc)
         = do env <- get
              (n', sc') <-
                    if n `elem` env
                       then do let n' = uniqueName n (env ++ inScope)
                               return (n', shadow n n' sc)
                       else return (n, sc)
              put (n' : env)
              ty' <- mkUniq ty; val' <- mkUniq val
              sc'' <- mkUniq sc'
              return $! PLet n' ty' val' sc''
  mkUniq (PApp fc t args)
         = do t' <- mkUniq t
              args' <- mapM mkUniqA args
              return $! PApp fc t' args'
  mkUniq (PAppBind fc t args)
         = do t' <- mkUniq t
              args' <- mapM mkUniqA args
              return $! PAppBind fc t' args'
  mkUniq (PCase fc t alts)
         = do t' <- mkUniq t
              alts' <- mapM (\(x,y)-> do x' <- mkUniq x; y' <- mkUniq y
                                         return (x', y')) alts
              return $! PCase fc t' alts'
  mkUniq (PPair fc p l r)
         = do l' <- mkUniq l; r' <- mkUniq r
              return $! PPair fc p l' r'
  mkUniq (PDPair fc l t r)
         = do l' <- mkUniq l; t' <- mkUniq t; r' <- mkUniq r
              return $! PDPair fc l' t' r'
  mkUniq (PAlternative b as)
         = liftM (PAlternative b) (mapM mkUniq as)
  mkUniq (PHidden t) = liftM PHidden (mkUniq t)
  mkUniq (PUnifyLog t) = liftM PUnifyLog (mkUniq t)
  mkUniq (PDisamb n t) = liftM (PDisamb n) (mkUniq t)
  mkUniq (PNoImplicits t) = liftM PNoImplicits (mkUniq t)
  mkUniq (PProof ts) = liftM PProof (mapM mkUniqT ts)
  mkUniq (PTactics ts) = liftM PTactics (mapM mkUniqT ts)
  mkUniq t = return t



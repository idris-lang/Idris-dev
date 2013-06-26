{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module IRTS.CodegenLLVM (codegenLLVM) where

import IRTS.CodegenCommon
import IRTS.Lang
import IRTS.Simplified
import qualified Core.TT as TT

import Util.System
import Paths_idris

import LLVM.General.Context
import LLVM.General.Diagnostic
import LLVM.General.AST
import LLVM.General.AST.AddrSpace
import qualified LLVM.General.Module as M
import qualified LLVM.General.AST.IntegerPredicate as IPred
import qualified LLVM.General.AST.Linkage as L
import qualified LLVM.General.AST.Visibility as V
import qualified LLVM.General.AST.CallingConvention as CC
import qualified LLVM.General.AST.Attribute as A
import qualified LLVM.General.AST.Global as G
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST.Float as F

import Data.List
import Data.Maybe
import Data.Word
import Data.Set (Set)
import qualified Data.Set as S
import Control.Applicative
import Control.Monad.RWS
import Control.Monad.Writer
import Control.Monad.State

import System.Info (arch)
import System.IO
import System.Directory (removeFile)
import System.FilePath ((</>))
import System.Process (rawSystem)
import System.Exit (ExitCode(..))
import Debug.Trace

codegenLLVM :: [(TT.Name, SDecl)] ->
               FilePath -> -- output file name
               OutputType ->
               IO ()
codegenLLVM defs file outty = withContext $ \context -> do
  let ast = codegen arch (map snd defs)
  result <- M.withModuleFromAST context ast (outputModule file outty)
  case result of
    Right _ -> return ()
    Left msg -> ierror msg

itWidth :: IntTy -> Word32
itWidth ITNative = 32
itWidth x = fromIntegral $ intTyWidth x

outputModule :: FilePath -> OutputType -> M.Module -> IO ()
outputModule file Raw    m = M.writeBitcodeToFile file m
outputModule file Object m = withTmpFile $ \bc -> do
  outputModule bc Raw m
  exit <- rawSystem "llc" ["-filetype=obj", "--disable-fp-elim", "-o", file, bc]
  when (exit /= ExitSuccess) $ ierror "FAILURE: Object generation"
outputModule file Executable m = withTmpFile $ \obj -> do
  outputModule obj Object m
  cc <- getCC
  defs <- (</> "llvm" </> "libidris_rts.a") <$> getDataDir
  exit <- rawSystem cc [obj, defs, "-lm", "-lgmp", "-lgc", "-o", file]
  when (exit /= ExitSuccess) $ ierror "FAILURE: Linking"

withTmpFile :: (FilePath -> IO a) -> IO a
withTmpFile f = do
  (path, handle) <- tempfile
  hClose handle
  result <- f path
  removeFile path
  return result

ierror :: String -> a
ierror msg = error $ "INTERNAL ERROR: IRTS.CodegenLLVM: " ++ msg

mainDef :: Global
mainDef =
    functionDefaults
    { G.returnType = IntegerType 32
    , G.parameters =
        ([ Parameter (IntegerType 32) (Name "argc") []
         , Parameter (PointerType (PointerType (IntegerType 8) (AddrSpace 0)) (AddrSpace 0)) (Name "argv") []
         ], False)
    , G.name = Name "main"
    , G.basicBlocks =
        [ BasicBlock (UnName 0)
          [ UnName 1 := idrCall "{runMain0}" [] ] -- TODO: Set GMP memory functions
          (Do $ Ret (Just (ConstantOperand (C.Int 32 0))) [])
        ]}

initDefs :: String -> [Definition]
initDefs tgt =
    [ TypeDefinition (Name "valTy")
      (Just $ StructureType False
                [ IntegerType 32
                , ArrayType 0 (PointerType valueType (AddrSpace 0))
                ])
    , TypeDefinition (Name "mpz")
        (Just $ StructureType False
                  [ IntegerType 32
                  , IntegerType 32
                  , PointerType intPtr (AddrSpace 0)
                  ])
    , GlobalDefinition $ globalVariableDefaults
      { G.name = Name "__idris_intFmtStr"
      , G.linkage = L.Internal
      , G.isConstant = True
      , G.hasUnnamedAddr = True
      , G.type' = ArrayType 5 (IntegerType 8)
      , G.initializer = Just $ C.Array (IntegerType 8) (map (C.Int 8 . fromIntegral . fromEnum) "%lld" ++ [C.Int 8 0])
      }
    , rtsFun "intStr" ptrI8 [IntegerType 64]
        [ BasicBlock (UnName 0)
          [ UnName 1 := simpleCall "GC_malloc_atomic" [ConstantOperand (C.Int (fromInteger $ tgtWordSize tgt) 12)]
          , UnName 2 := simpleCall "snprintf"
                       [ LocalReference (UnName 1)
                       , ConstantOperand (C.Int (fromInteger $ tgtWordSize tgt) 12)
                       , ConstantOperand $ C.GetElementPtr True (C.GlobalReference . Name $ "__idris_intFmtStr") [C.Int 32 0, C.Int 32 0]
                       , LocalReference (UnName 0)
                       ]
          ]
          (Do $ Ret (Just (LocalReference (UnName 1))) [])
        ]
    , exfun "llvm.trap" VoidType [] False
    , exfun "snprintf" (IntegerType 32) [ptrI8, intPtr, ptrI8] True
    , exfun "strcmp" (IntegerType 32) [ptrI8, ptrI8] False
    , exfun "strlen" intPtr [ptrI8] False
    , exfun "memcpy" ptrI8 [ptrI8, ptrI8, intPtr] False
    , exfun "GC_malloc" ptrI8 [intPtr] False
    , exfun "GC_malloc_atomic" ptrI8 [intPtr] False
    , exfun "__gmpz_init" VoidType [pmpz] False
    , exfun "__gmpz_init_set_str" (IntegerType 32) [pmpz, ptrI8, IntegerType 32] False
    , exfun "__gmpz_get_str" ptrI8 [ptrI8, IntegerType 32, pmpz] False
    , exfun "__gmpz_cmp" (IntegerType 32) [pmpz, pmpz] False
    , exfun "mpz_get_ull" (IntegerType 64) [pmpz] False
    , GlobalDefinition mainDef
    ] ++ map mpzBinFun ["add", "sub", "mul", "fdiv_q", "fdiv_r", "and", "ior", "xor"]
    where
      intPtr = IntegerType (fromInteger $ tgtWordSize tgt)
      ptrI8 = PointerType (IntegerType 8) (AddrSpace 0)
      pmpz = PointerType mpzTy (AddrSpace 0)

      mpzBinFun n = exfun ("__gmpz_" ++ n) VoidType [pmpz, pmpz, pmpz] False

      rtsFun :: String -> Type -> [Type] -> [BasicBlock] -> Definition
      rtsFun name rty argtys def =
          GlobalDefinition $ functionDefaults
                               { G.linkage = L.Internal
                               , G.returnType = rty
                               , G.parameters = (flip map argtys $ \ty -> Parameter ty (UnName 0) [], False)
                               , G.name = Name $ "__idris_" ++ name
                               , G.basicBlocks = def
                               }
      
      exfun :: String -> Type -> [Type] -> Bool -> Definition
      exfun name rty argtys vari =
          GlobalDefinition $ functionDefaults
                               { G.returnType = rty
                               , G.name = Name name
                               , G.parameters = (flip map argtys $ \ty -> Parameter ty (UnName 0) [], vari)
                               }

codegen :: String -> [SDecl] -> Module
codegen tgt defs = Module "idris" Nothing Nothing (initDefs tgt ++ globals ++ gendefs)
    where
      ((gendefs, globals), _) = (runState . runWriterT) (mapM cgDef defs) 0

valueType :: Type
valueType = NamedTypeReference (Name "valTy")

nullValue :: C.Constant
nullValue = C.Null (PointerType valueType (AddrSpace 0))

primTy :: Type -> Type
primTy inner = StructureType False [IntegerType 8, inner]

mpzTy :: Type
mpzTy = NamedTypeReference (Name "mpz")

conType :: Word64 -> Type
conType nargs = StructureType False
                [ IntegerType 32
                , ArrayType nargs (PointerType valueType (AddrSpace 0))
                ]

type Modgen = WriterT [Definition] (State Word)

cgDef :: SDecl -> Modgen Definition
cgDef (SFun name argNames _ expr) = do
  nextGlobal <- get
  let (_, CGS { nextGlobalName = nextGlobal' }, (allocas, bbs, globals)) =
          runRWS (do r <- cgExpr expr
                     case r of
                       Nothing -> terminate $ Unreachable []
                       Just r' -> terminate $ Ret (Just r') [])
                 (CGR arch (Name . show $ name))
                 (CGS 0 nextGlobal (Name "begin") [] (map (Just . LocalReference . Name . show) argNames) S.empty)
      entryTerm = case bbs of
                    [] -> Do $ Ret Nothing []
                    BasicBlock n _ _:_ -> Do $ Br n []
  tell globals
  put nextGlobal'
  return . GlobalDefinition $ functionDefaults
             { G.linkage = L.Internal
             , G.callingConvention = CC.Fast
             , G.name = Name (show name)
             , G.returnType = PointerType valueType (AddrSpace 0)
             , G.parameters = (flip map argNames $ \argName ->
                                   Parameter (PointerType valueType (AddrSpace 0)) (Name (show argName)) []
                              , False)
             , G.basicBlocks =
                 BasicBlock (Name "entry")
                                 (map (\(n, t) -> n := Alloca t Nothing 0 []) allocas)
                                 entryTerm
                 : bbs
             }

type CGW = ([(Name, Type)], [BasicBlock], [Definition])

type Env = [Maybe Operand]

data CGS = CGS { nextName :: Word
               , nextGlobalName :: Word
               , currentBlockName :: Name
               , instAccum :: [Named Instruction]
               , lexenv :: Env
               , foreignSyms :: Set String
               }

data CGR = CGR { target :: String
               , funcName :: Name }

type Codegen = RWS CGR CGW CGS

getGlobalUnName :: Codegen Name
getGlobalUnName = do
  i <- gets nextGlobalName
  modify $ \s -> s { nextGlobalName = 1 + i }
  return (UnName i)

getUnName :: Codegen Name
getUnName = do
  i <- gets nextName
  modify $ \s -> s { nextName = 1 + i }
  return (UnName i)

getName :: String -> Codegen Name
getName n = do
  i <- gets nextName
  modify $ \s -> s { nextName = 1 + i }
  return (Name $ n ++ show i)

alloca :: Name -> Type -> Codegen ()
alloca n t = tell ([(n, t)], [], [])

terminate :: Terminator -> Codegen ()
terminate term = do
  name <- gets currentBlockName
  insts <- gets instAccum
  modify $ \s -> s { instAccum = ierror "Not in a block"
                   , currentBlockName = ierror "Not in a block" }
  tell ([], [BasicBlock name insts (Do term)], [])

newBlock :: Name -> Codegen ()
newBlock name = modify $ \s -> s { instAccum = []
                                 , currentBlockName = name
                                 }

inst :: Instruction -> Codegen Operand
inst i = do
  n <- getUnName
  modify $ \s -> s { instAccum = instAccum s ++ [n := i] }
  return $ LocalReference n

ninst :: String -> Instruction -> Codegen Operand
ninst name i = do
  n <- getName name
  modify $ \s -> s { instAccum = instAccum s ++ [n := i] }
  return $ LocalReference n

inst' :: Instruction -> Codegen ()
inst' i = modify $ \s -> s { instAccum = instAccum s ++ [Do i] }

insts :: [Named Instruction] -> Codegen ()
insts is = modify $ \s -> s { instAccum = instAccum s ++ is }

var :: LVar -> Codegen (Maybe Operand)
var (Loc level) = (!! level) <$> gets lexenv
var (Glob n) = return . Just . ConstantOperand . C.GlobalReference . Name $ show n

binds :: Env -> Codegen (Maybe Operand) -> Codegen (Maybe Operand)
binds vals cg = do
  envLen <- length <$> gets lexenv
  modify $ \s -> s { lexenv = lexenv s ++ vals }
  value <- cg
  modify $ \s -> s { lexenv = take envLen $ lexenv s }
  return value

replaceElt :: Int -> a -> [a] -> [a]
replaceElt _ val [] = error "replaceElt: Ran out of list"
replaceElt 0 val (x:xs) = val:xs
replaceElt n val (x:xs) = x : replaceElt (n-1) val xs

alloc' :: Operand -> Codegen Operand
alloc' size = inst $ simpleCall "GC_malloc" [size]

allocAtomic :: Operand -> Codegen Operand
allocAtomic size = inst $ simpleCall "GC_malloc_atomic" [size]

alloc :: Type -> Codegen Operand
alloc ty = do
  size <- sizeOf ty
  mem <- alloc' size
  inst $ BitCast mem (PointerType ty (AddrSpace 0)) []

sizeOf :: Type -> Codegen Operand
sizeOf ty = ConstantOperand . C.PtrToInt
            (C.GetElementPtr True (C.Null (PointerType ty (AddrSpace 0))) [C.Int 32 1])
            . IntegerType . fromIntegral <$> getWordSize

tgtWordSize :: String -> Integer
tgtWordSize tgt = case tgt of
                    "x86_64" -> 64
                    "i386" -> 32

getWordSize :: Codegen Integer
getWordSize = tgtWordSize <$> asks target

cgExpr :: SExp -> Codegen (Maybe Operand)
cgExpr (SV v) = var v
cgExpr (SApp tailcall fname args) = do
  argSlots <- mapM var args
  case sequence argSlots of
    Nothing -> return Nothing
    Just argVals -> do
      fn <- var (Glob fname)
      Just <$> inst ((idrCall (show fname) argVals) { isTailCall = tailcall })
cgExpr (SLet _ varExpr bodyExpr) = do
  val <- cgExpr varExpr
  binds [val] $ cgExpr bodyExpr
cgExpr (SUpdate (Loc level) expr) = do
  val <- cgExpr expr
  modify $ \s -> s { lexenv = replaceElt level val (lexenv s) }
  return val
cgExpr (SCon tag name args) = do
  argSlots <- mapM var args
  case sequence argSlots of
    Nothing -> return Nothing
    Just argVals -> do
      con <- alloc . conType . fromIntegral . length $ argVals
      tagPtr <- inst $ GetElementPtr True con [ConstantOperand (C.Int 32 0), ConstantOperand (C.Int 32 0)] []
      inst' $ Store False tagPtr (ConstantOperand (C.Int 32 (fromIntegral tag))) Nothing 0 []
      forM_ (zip argVals [0..]) $ \(arg, i) -> do
        ptr <- inst $ GetElementPtr True con [ ConstantOperand (C.Int 32 0)
                                             , ConstantOperand (C.Int 32 1)
                                             , ConstantOperand (C.Int 32 i)] []
        inst' $ Store False ptr arg Nothing 0 []
      Just <$> inst (BitCast con (PointerType valueType (AddrSpace 0)) [])
cgExpr (SCase inspect alts) = do
  val <- var inspect
  case val of
    Nothing -> return Nothing
    Just v -> cgCase v alts
cgExpr (SChkCase inspect alts) = do
  mval <- var inspect
  case mval of
    Nothing -> return Nothing
    Just val ->
        do endBBN <- getName "endChkCase"
           notNullBBN <- getName "notNull"
           originBlock <- gets currentBlockName
           isNull <- inst $ ICmp IPred.EQ val (ConstantOperand nullValue) []
           terminate $ CondBr isNull endBBN notNullBBN []
           newBlock notNullBBN
           ptr <- inst $ BitCast val (PointerType (IntegerType 8) (AddrSpace 0)) []
           flag <- inst $ Load False ptr Nothing 0 []
           isVal <- inst $ ICmp IPred.EQ flag (ConstantOperand (C.Int 8 (-1))) []
           conBBN <- getName "constructor"
           terminate $ CondBr isVal endBBN conBBN []
           newBlock conBBN
           result <- cgCase val alts
           caseExitBlock <- gets currentBlockName
           case result of
             Nothing -> do
               terminate $ Unreachable []
               newBlock endBBN
               return $ Just val
             Just caseVal -> do
               terminate $ Br endBBN []
               newBlock endBBN
               Just <$> inst (Phi (PointerType valueType (AddrSpace 0))
                              [(val, originBlock), (val, notNullBBN), (caseVal, caseExitBlock)] [])
cgExpr (SProj conVar idx) = do
  val <- var conVar
  case val of
    Nothing -> return Nothing
    Just v ->
        do ptr <- inst $ GetElementPtr True v
                  [ ConstantOperand (C.Int 32 0)
                  , ConstantOperand (C.Int 32 1)
                  , ConstantOperand (C.Int 32 (fromIntegral idx))
                  ] []
           Just <$> inst (Load False ptr Nothing 0 [])
cgExpr (SConst c) = Just <$> cgConst c
cgExpr (SForeign LANG_C rty fname args) = do
  func <- ensureCDecl fname rty (map fst args)
  argVals <- forM args $ \(fty, v) -> do
               v' <- var v
               case v' of
                 Just val -> return $ Just (fty, val)
                 Nothing -> return Nothing
  case sequence argVals of
    Nothing -> return Nothing
    Just argVals' -> do
      argUVals <- mapM (uncurry unbox) argVals'
      result <- inst Call { isTailCall = False
                          , callingConvention = CC.C
                          , returnAttributes = []
                          , function = Right func
                          , arguments = map (\v -> (v, [])) argUVals
                          , functionAttributes = []
                          , metadata = []
                          }
      Just <$> box rty result
cgExpr (SOp fn args) = do
  argVals <- mapM var args
  case sequence argVals of
    Just ops -> Just <$> cgOp fn ops
    Nothing -> return Nothing
cgExpr SNothing = return . Just . ConstantOperand $ nullValue
cgExpr (SError msg) = do -- TODO: Print message
  str <- addGlobal' (ArrayType (2 + fromIntegral (length msg)) (IntegerType 8))
         (cgConst' (TT.Str (msg ++ "\n")))
  inst' $ simpleCall "putStr" [ConstantOperand $ C.GetElementPtr True str [ C.Int 32 0
                                                                          , C.Int 32 0]]
  inst' Call { isTailCall = True
             , callingConvention = CC.C
             , returnAttributes = []
             , function = Right . ConstantOperand . C.GlobalReference . Name $ "llvm.trap"
             , arguments = []
             , functionAttributes = [A.NoReturn]
             , metadata = []
             }
  return Nothing

cgCase :: Operand -> [SAlt] -> Codegen (Maybe Operand)
cgCase val alts =
    case find isConstCase alts of
      Just (SConstCase (TT.BI _) _) -> cgChainCase val defExp constAlts
      Just (SConstCase (TT.Str _) _) -> cgChainCase val defExp constAlts
      Just (SConstCase _ _) -> cgPrimCase val defExp constAlts
      Nothing -> cgConCase val defExp conAlts
    where
      defExp = getDefExp =<< find isDefCase alts
      constAlts = filter isConstCase alts
      conAlts = filter isConCase alts
                
      isConstCase (SConstCase {}) = True
      isConstCase _ = False

      isConCase (SConCase {}) = True
      isConCase _ = False

      isDefCase (SDefaultCase _) = True
      isDefCase _ = False

      getDefExp (SDefaultCase e) = Just e
      getDefExp _ = Nothing

cgPrimCase :: Operand -> Maybe SExp -> [SAlt] -> Codegen (Maybe Operand)
cgPrimCase caseValPtr defExp alts = do
  let caseTy = case head alts of
                 SConstCase (TT.I _)   _ -> IntegerType 32
                 SConstCase (TT.B8 _)  _ -> IntegerType 8
                 SConstCase (TT.B16 _) _ -> IntegerType 16
                 SConstCase (TT.B32 _) _ -> IntegerType 32
                 SConstCase (TT.B64 _) _ -> IntegerType 64
                 SConstCase (TT.Fl _)  _ -> FloatingPointType 64 IEEE
                 SConstCase (TT.Ch _)  _ -> IntegerType 32
  realPtr <- inst $ BitCast caseValPtr (PointerType (primTy caseTy) (AddrSpace 0)) []
  valPtr <- inst $ GetElementPtr True realPtr [ConstantOperand (C.Int 32 0), ConstantOperand (C.Int 32 1)] []
  caseVal <- inst $ Load False valPtr Nothing 0 []
  defBlockName <- getName "default"
  exitBlockName <- getName "caseExit"
  namedAlts <- mapM (\a -> do n <- nameAlt defBlockName a; return (n, a)) alts
  terminate $ Switch caseVal defBlockName (map (\(n, SConstCase c _) -> (cgConst' c, n)) namedAlts) []
  initEnv <- gets lexenv
  defResult <- cgDefaultAlt exitBlockName defBlockName defExp
  results <- forM namedAlts $ \(name, SConstCase _ exp) -> cgAlt initEnv exitBlockName name Nothing exp
  finishCase initEnv exitBlockName (defResult:results)

cgConCase :: Operand -> Maybe SExp -> [SAlt] -> Codegen (Maybe Operand)
cgConCase con defExp alts = do
  tagPtr <- inst $ GetElementPtr True con [ConstantOperand (C.Int 32 0), ConstantOperand (C.Int 32 0)] []
  tag <- inst $ Load False tagPtr Nothing 0 []
  defBlockName <- getName "default"
  exitBlockName <- getName "caseExit"
  namedAlts <- mapM (\a -> do n <- nameAlt defBlockName a; return (n, a)) alts
  terminate $ Switch tag defBlockName (map (\(n, SConCase _ tag _ _ _) ->
                                                (C.Int 32 (fromIntegral tag), n)) namedAlts) []
  initEnv <- gets lexenv
  defResult <- cgDefaultAlt exitBlockName defBlockName defExp
  results <- forM namedAlts $ \(name, SConCase _ _ _ argns exp) ->
             cgAlt initEnv exitBlockName name (Just (con, map show argns)) exp
  finishCase initEnv exitBlockName (defResult:results)

cgChainCase :: Operand -> Maybe SExp -> [SAlt] -> Codegen (Maybe Operand)
cgChainCase caseValPtr defExp alts = do
  let (caseTy, comparator) =
          case head alts of
            SConstCase (TT.BI _) _ -> (FInt ITBig, "__gmpz_cmp")
            SConstCase (TT.Str _) _ -> (FString, "strcmp")
  caseVal <- unbox caseTy caseValPtr
  defBlockName <- getName "default"
  exitBlockName <- getName "caseExit"
  namedAlts <- mapM (\a -> do n <- nameAlt defBlockName a; return (n, a)) alts
  initEnv <- gets lexenv
  results <- forM namedAlts $ \(name, SConstCase c e) ->
             do const <- unbox caseTy =<< cgConst c
                cmp <- inst $ simpleCall comparator [const, caseVal]
                cmpResult <- inst $ ICmp IPred.EQ cmp (ConstantOperand (C.Int 32 0)) []
                elseName <- getName "else"
                terminate $ CondBr cmpResult name elseName []
                result <- cgAlt initEnv exitBlockName name Nothing e
                newBlock elseName
                return result
  modify $ \s -> s { lexenv = initEnv }
  defaultVal <- cgExpr (fromMaybe (SError "Inexhaustive case failure") defExp)
  defaultBlock <- gets currentBlockName
  defaultEnv <- gets lexenv
  defResult <- case defaultVal of
                 Just v -> do
                   terminate $ Br exitBlockName []
                   return $ Just (v, defaultBlock, defaultEnv)
                 Nothing -> do
                   terminate $ Unreachable []
                   return Nothing
  finishCase initEnv exitBlockName (defResult:results)

finishCase :: Env -> Name -> [Maybe (Operand, Name, Env)] -> Codegen (Maybe Operand)
finishCase initEnv exitBlockName results = do
  let definedResults = mapMaybe id results
  case definedResults of
    [] -> do modify $ \s -> s { lexenv = initEnv }
             return Nothing
    xs -> do
      newBlock exitBlockName
      mergeEnvs $ map (\(_, altBlock, altEnv) -> (altBlock, altEnv)) xs
      Just <$> inst (Phi (PointerType valueType (AddrSpace 0))
                (map (\(altVal, altBlock, _) -> (altVal, altBlock)) xs) [])


cgDefaultAlt :: Name -> Name -> Maybe SExp -> Codegen (Maybe (Operand, Name, Env))
cgDefaultAlt exitName name exp = do
  newBlock name
  val <- cgExpr (fromMaybe (SError "Inexhaustive case failure") exp)
  env <- gets lexenv
  block <- gets currentBlockName
  case val of
    Just v ->
        do terminate $ Br exitName []
           return $ Just (v, block, env)
    Nothing ->
        do terminate $ Unreachable []
           return Nothing

cgAlt :: Env -> Name -> Name -> Maybe (Operand, [String]) -> SExp
      -> Codegen (Maybe (Operand, Name, Env))
cgAlt initEnv exitBlockName name destr exp = do
  modify $ \s -> s { lexenv = initEnv }
  newBlock name
  locals <- case destr of
              Nothing -> return []
              Just (con, argns) ->
                  forM (zip argns [0..]) $ \(argName, i) ->
                      do ptr <- inst $ GetElementPtr True con [ ConstantOperand (C.Int 32 0)
                                                              , ConstantOperand (C.Int 32 1)
                                                              , ConstantOperand (C.Int 32 i)] []
                         Just <$> ninst argName (Load False ptr Nothing 0 [])
  altVal <- binds locals $ cgExpr exp
  altEnv <- gets lexenv
  altBlock <- gets currentBlockName
  case altVal of
    Just v -> do
      terminate $ Br exitBlockName []
      return $ Just (v, altBlock, altEnv)
    Nothing -> do
      terminate $ Unreachable []
      return Nothing

mergeEnvs :: [(Name, Env)] -> Codegen ()
mergeEnvs es = do
  let vars = transpose
             . map (\(block, env) -> map (\x -> (x, block)) env)
             $ es
  env <- forM vars $ \var ->
         case var of
           [] -> ierror "mergeEnvs: impossible"
           [(v, _)] -> return v
           vs@((v, _):_)
                  | all (== v) (map fst vs) -> return v
                  | otherwise ->
                      let valid = map (\(a, b) -> (fromJust a, b)) . filter (isJust . fst) $ vs in
                      Just <$> inst (Phi (PointerType valueType (AddrSpace 0)) valid [])
  modify $ \s -> s { lexenv = env }

nameAlt :: Name -> SAlt -> Codegen Name
nameAlt d (SDefaultCase _) = return d
nameAlt _ (SConCase _ _ name _ _) = getName (show name)
nameAlt _ (SConstCase const _) = getName (show const)

box :: FType -> Operand -> Codegen Operand
box FUnit _ = return $ ConstantOperand nullValue
box fty fval = do
  val <- alloc (primTy (ftyToTy fty))
  tagptr <- inst $ GetElementPtr True val [ConstantOperand (C.Int 32 0), ConstantOperand (C.Int 32 0)] []
  valptr <- inst $ GetElementPtr True val [ConstantOperand (C.Int 32 0), ConstantOperand (C.Int 32 1)] []
  inst' $ Store False tagptr (ConstantOperand (C.Int 8 (-1))) Nothing 0 []
  inst' $ Store False valptr fval Nothing 0 []
  inst $ BitCast val (PointerType valueType (AddrSpace 0)) []

unbox :: FType -> Operand -> Codegen Operand
unbox FUnit x = return x
unbox fty bval = do
  val <- inst $ BitCast bval (PointerType (primTy (ftyToTy fty)) (AddrSpace 0)) []
  fvalptr <- inst $ GetElementPtr True val [ConstantOperand (C.Int 32 0), ConstantOperand (C.Int 32 1)] []
  inst $ Load False fvalptr Nothing 0 []

cgConst' :: TT.Const -> C.Constant
cgConst' (TT.I i) = C.Int 32 (fromIntegral i)
cgConst' (TT.B8  i) = C.Int 8  (fromIntegral i)
cgConst' (TT.B16 i) = C.Int 16 (fromIntegral i)
cgConst' (TT.B32 i) = C.Int 32 (fromIntegral i)
cgConst' (TT.B64 i) = C.Int 64 (fromIntegral i)
cgConst' (TT.BI i) = C.Array (IntegerType 8) (map (C.Int 8 . fromIntegral . fromEnum) (show i) ++ [C.Int 8 0])
cgConst' (TT.Fl f) = C.Float (F.Double f)
cgConst' (TT.Ch c) = C.Int 32 . fromIntegral . fromEnum $ c
cgConst' (TT.Str s) = C.Array (IntegerType 8) (map (C.Int 8 . fromIntegral . fromEnum) s ++ [C.Int 8 0])
cgConst' x = ierror $ "Unsupported constant: " ++ show x

cgConst :: TT.Const -> Codegen Operand
cgConst c@(TT.I _) = box (FInt ITNative) (ConstantOperand $ cgConst' c)
cgConst c@(TT.B8  _) = box (FInt IT8) (ConstantOperand $ cgConst' c)
cgConst c@(TT.B16 _) = box (FInt IT16) (ConstantOperand $ cgConst' c)
cgConst c@(TT.B32 _) = box (FInt IT32) (ConstantOperand $ cgConst' c)
cgConst c@(TT.B64 _) = box (FInt IT64) (ConstantOperand $ cgConst' c)
cgConst c@(TT.Fl _) = box FDouble (ConstantOperand $ cgConst' c)
cgConst c@(TT.Ch _) = box FChar (ConstantOperand $ cgConst' c)
cgConst c@(TT.Str s) = do
  str <- addGlobal' (ArrayType (1 + fromIntegral (length s)) (IntegerType 8)) (cgConst' c)
  box FString (ConstantOperand $ C.GetElementPtr True str [C.Int 32 0, C.Int 32 0])
cgConst c@(TT.BI i) = do
  str <- addGlobal' (ArrayType (1 + fromInteger (numDigits 10 i)) (IntegerType 8)) (cgConst' c)
  mpz <- alloc mpzTy
  inst $ simpleCall "__gmpz_init_set_str" [mpz
                                          , ConstantOperand $ C.GetElementPtr True str [ C.Int 32 0, C.Int 32 0]
                                          , ConstantOperand $ C.Int 32 10
                                          ]
  box (FInt ITBig) mpz
cgConst x = return $ ConstantOperand nullValue

numDigits :: Integer -> Integer -> Integer
numDigits b n = 1 + fst (ilog b n) where
    ilog b n
        | n < b     = (0, n)
        | otherwise = let (e, r) = ilog (b*b) n
                      in  if r < b then (2*e, r) else (2*e+1, r `div` b)

addGlobal :: Global -> Codegen ()
addGlobal def = tell ([], [], [GlobalDefinition def])

addGlobal' :: Type -> C.Constant -> Codegen C.Constant
addGlobal' ty val = do
  name <- getGlobalUnName
  addGlobal $ globalVariableDefaults
                { G.name = name
                , G.linkage = L.Internal
                , G.hasUnnamedAddr = True
                , G.isConstant = True
                , G.type' = ty
                , G.initializer = Just val
                }
  return . C.GlobalReference $ name
  

ensureCDecl :: String -> FType -> [FType] -> Codegen Operand
ensureCDecl name rty argtys = do
  syms <- gets foreignSyms
  unless (S.member name syms) $
         do addGlobal (ffunDecl name rty argtys)
            modify $ \s -> s { foreignSyms = S.insert name (foreignSyms s) }
  return $ ConstantOperand (C.GlobalReference (Name name))

ffunDecl :: String -> FType -> [FType] -> Global
ffunDecl name rty argtys =
    functionDefaults
    { G.returnType = ftyToTy rty
    , G.name = Name name
    , G.parameters = (flip map argtys $ \fty ->
                          Parameter (ftyToTy fty) (UnName 0) []
                     , False)
    }

ftyToTy :: FType -> Type
ftyToTy (FInt ITNative) = IntegerType 32
ftyToTy (FInt ITBig) = PointerType mpzTy (AddrSpace 0)
ftyToTy (FInt ty) = IntegerType (itWidth ty)
ftyToTy FChar = IntegerType 32
ftyToTy FString = PointerType (IntegerType 8) (AddrSpace 0)
ftyToTy FUnit = VoidType
ftyToTy FPtr = PointerType (IntegerType 8) (AddrSpace 0)
ftyToTy FDouble = FloatingPointType 64 IEEE
ftyToTy FAny = valueType

cgOp :: PrimFn -> [Operand] -> Codegen Operand
cgOp (LTrunc ITBig ity) [x] = do
  nx <- unbox (FInt ITBig) x
  val <- inst $ simpleCall "mpz_get_ull" [nx]
  v <- case ity of
         IT64 -> return val
         _ -> inst $ Trunc val (IntegerType $ itWidth ity) []
  box (FInt ity) v

cgOp (LLt    ITBig) [x,y] = mpzCmp IPred.SLT x y
cgOp (LLe    ITBig) [x,y] = mpzCmp IPred.SLE x y
cgOp (LEq    ITBig) [x,y] = mpzCmp IPred.EQ  x y
cgOp (LGe    ITBig) [x,y] = mpzCmp IPred.SGE x y
cgOp (LGt    ITBig) [x,y] = mpzCmp IPred.SGT x y
cgOp (LPlus  ITBig) [x,y] = mpzBin "add" x y
cgOp (LMinus ITBig) [x,y] = mpzBin "sub" x y
cgOp (LTimes ITBig) [x,y] = mpzBin "mul" x y
cgOp (LSDiv  ITBig) [x,y] = mpzBin "fdiv_q" x y
cgOp (LSRem  ITBig) [x,y] = mpzBin "fdiv_r" x y
cgOp (LAnd   ITBig) [x,y] = mpzBin "and" x y
cgOp (LOr    ITBig) [x,y] = mpzBin "ior" x y
cgOp (LXOr   ITBig) [x,y] = mpzBin "xor" x y

cgOp (LTrunc from to) [x] | itWidth from > itWidth to = iCoerce Trunc from to x
cgOp (LZExt from to) [x] | itWidth from < itWidth to = iCoerce ZExt from to x
cgOp (LSExt from to) [x] | itWidth from < itWidth to = iCoerce SExt from to x

cgOp (LLt    ity) [x,y] = iCmp ity IPred.SLT x y
cgOp (LLe    ity) [x,y] = iCmp ity IPred.SLE x y
cgOp (LEq    ity) [x,y] = iCmp ity IPred.EQ  x y
cgOp (LGe    ity) [x,y] = iCmp ity IPred.SGE x y
cgOp (LGt    ity) [x,y] = iCmp ity IPred.SGT x y
cgOp (LPlus  ity) [x,y] = ibin ity x y (Add False False)
cgOp (LMinus ity) [x,y] = ibin ity x y (Sub False False)
cgOp (LTimes ity) [x,y] = ibin ity x y (Mul False False)
cgOp (LUDiv  ity) [x,y] = ibin ity x y (UDiv True)
cgOp (LURem  ity) [x,y] = ibin ity x y URem
cgOp (LSDiv  ity) [x,y] = ibin ity x y (SDiv True)
cgOp (LSRem  ity) [x,y] = ibin ity x y SRem
cgOp (LAnd   ity) [x,y] = ibin ity x y And
cgOp (LOr    ity) [x,y] = ibin ity x y Or
cgOp (LXOr   ity) [x,y] = ibin ity x y Xor

cgOp LStrEq [x,y] = do
  x' <- unbox FString x
  y' <- unbox FString y
  cmp <- inst $ simpleCall "strcmp" [x', y']
  flag <- inst $ ICmp IPred.EQ cmp (ConstantOperand (C.Int 32 0)) []
  val <- inst $ ZExt flag (IntegerType 32) []
  box (FInt IT32) val

cgOp (LIntStr ITBig) [x] = do
  x' <- unbox (FInt ITBig) x
  ustr <- inst $ simpleCall "__gmpz_get_str"
          [ ConstantOperand (C.Null (PointerType (IntegerType 8) (AddrSpace 0)))
          , ConstantOperand (C.Int 32 10)
          , x'
          ]
  box FString ustr
cgOp (LIntStr ity) [x] = do
  x' <- unbox (FInt ity) x
  x'' <- if itWidth ity < 64
         then inst $ SExt x' (IntegerType 64) []
         else return x'
  box FString =<< inst (idrCall "__idris_intStr" [x''])

cgOp LStrConcat [x,y] = cgStrCat x y
cgOp prim args = ierror $ "Unimplemented primitive: [" ++ show prim ++ "]("
                  ++ intersperse ',' (take (length args) ['a'..]) ++ ")"

iCoerce :: (Operand -> Type -> InstructionMetadata -> Instruction) -> IntTy -> IntTy -> Operand -> Codegen Operand
iCoerce operator from to x = do
  x' <- unbox (FInt from) x
  x'' <- inst $ operator x' (IntegerType $ itWidth to) []
  box (FInt to) x''

cgStrCat :: Operand -> Operand -> Codegen Operand
cgStrCat x y = do
  x' <- unbox FString x
  y' <- unbox FString y
  xlen <- inst $ simpleCall "strlen" [x']
  ylen <- inst $ simpleCall "strlen" [y']
  zlen <- inst $ Add False True xlen ylen []
  ws <- fromIntegral <$> getWordSize
  total <- inst $ Add False True zlen (ConstantOperand (C.Int ws 1)) []
  mem <- allocAtomic total
  inst $ simpleCall "memcpy" [mem, x', xlen]
  i <- inst $ PtrToInt mem (IntegerType ws) []
  offi <- inst $ Add False True i xlen []
  offp <- inst $ IntToPtr offi (PointerType (IntegerType 8) (AddrSpace 0)) []
  inst $ simpleCall "memcpy" [offp, y', ylen]
  j <- inst $ PtrToInt offp (IntegerType ws) []
  offj <- inst $ Add False True j ylen []
  end <- inst $ IntToPtr offj (PointerType (IntegerType 8) (AddrSpace 0)) []
  inst' $ Store False end (ConstantOperand (C.Int 8 0)) Nothing 0 []
  box FString mem
  
ibin :: IntTy -> Operand -> Operand
     -> (Operand -> Operand -> InstructionMetadata -> Instruction) -> Codegen Operand
ibin ity x y instCon = do
  nx <- unbox (FInt ity) x
  ny <- unbox (FInt ity) y
  nr <- inst $ instCon nx ny []
  box (FInt ity) nr

iCmp :: IntTy -> IPred.IntegerPredicate -> Operand -> Operand -> Codegen Operand
iCmp ity pred x y = do
  nx <- unbox (FInt ity) x
  ny <- unbox (FInt ity) y
  nr <- inst $ ICmp pred nx ny []
  nr' <- inst $ ZExt nr (IntegerType 32) []
  box (FInt IT32) nr'

mpzBin :: String -> Operand -> Operand -> Codegen Operand
mpzBin name x y = do
  nx <- unbox (FInt ITBig) x
  ny <- unbox (FInt ITBig) y
  nz <- alloc mpzTy
  inst' $ simpleCall "__gmpz_init" [nz]
  inst' $ simpleCall ("__gmpz_" ++ name) [nz, nx, ny]
  box (FInt ITBig) nz

mpzCmp :: IPred.IntegerPredicate -> Operand -> Operand -> Codegen Operand
mpzCmp pred x y = do
  nx <- unbox (FInt ITBig) x
  ny <- unbox (FInt ITBig) y
  cmp <- inst $ simpleCall "__gmpz_cmp" [nx, ny]
  result <- inst $ ICmp pred cmp (ConstantOperand (C.Int 32 0)) []
  i <- inst $ ZExt result (IntegerType 32) []
  box (FInt IT32) i

simpleCall :: String -> [Operand] -> Instruction
simpleCall name args =
    Call { isTailCall = False
         , callingConvention = CC.C
         , returnAttributes = []
         , function = Right . ConstantOperand . C.GlobalReference . Name $ name
         , arguments = map (\x -> (x, [])) args
         , functionAttributes = []
         , metadata = []
         }

idrCall :: String -> [Operand] -> Instruction
idrCall name args =
    Call { isTailCall = False
         , callingConvention = CC.Fast
         , returnAttributes = []
         , function = Right . ConstantOperand . C.GlobalReference . Name $ name
         , arguments = map (\x -> (x, [])) args
         , functionAttributes = []
         , metadata = []
         }
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
module IRTS.CodegenRuby (codegenRuby, RubyTarget(..)) where

import IRTS.Ruby.AST

import Idris.AbsSyntax hiding (TypeCase)
import IRTS.Bytecode
import IRTS.Lang
import IRTS.Simplified
import IRTS.CodegenCommon
import Idris.Core.TT
import IRTS.System
import Util.System

import Control.Arrow
import Control.Monad (mapM)
import Control.Applicative ((<$>), (<*>), pure)
import Control.Monad.RWS hiding (mapM)
import Control.Monad.State
import Data.Char
import Numeric
import Data.List
import Data.Maybe
import Data.Word
import Data.Traversable hiding (mapM)
import System.IO
import System.Directory

import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Text.IO as TIO


data CompileInfo = CompileInfo { compileInfoApplyCases  :: [Int]
                               , compileInfoEvalCases   :: [Int]
                               , compileInfoNeedsBigInt :: Bool
                               }


initCompileInfo :: [(Name, [BC])] -> CompileInfo
initCompileInfo bc =
  CompileInfo (collectCases "APPLY" bc) (collectCases "EVAL" bc) (lookupBigInt bc)
  where
    lookupBigInt :: [(Name, [BC])] -> Bool
    lookupBigInt = any (needsBigInt . snd)
      where
        needsBigInt :: [BC] -> Bool
        needsBigInt bc = or $ map testBCForBigInt bc
          where
            testBCForBigInt :: BC -> Bool
            testBCForBigInt (ASSIGNCONST _ c)  =
              testConstForBigInt c

            testBCForBigInt (CONSTCASE _ c d) =
                 maybe False needsBigInt d
              || (or $ map (needsBigInt . snd) c)
              || (or $ map (testConstForBigInt . fst) c)

            testBCForBigInt _ = False

            testConstForBigInt :: Const -> Bool
            testConstForBigInt (BI _)  = True
            testConstForBigInt (B64 _) = True
            testConstForBigInt _       = False


    collectCases :: String ->  [(Name, [BC])] -> [Int]
    collectCases fun bc = getCases $ findFunction fun bc

    findFunction :: String -> [(Name, [BC])] -> [BC]
    findFunction f ((MN 0 fun, bc):_)
      | fun == txt f = bc
    findFunction f (_:bc) = findFunction f bc

    getCases :: [BC] -> [Int]
    getCases = concatMap analyze
      where
        analyze :: BC -> [Int]
        analyze (CASE _ _ b _) = map fst b
        analyze _              = []


data RubyTarget = Ruby deriving Eq


codegenRuby :: CodeGenerator
codegenRuby ci =
  codegenRuby_all Ruby (simpleDecls ci)
    (includes ci) [] (outputFile ci) (outputType ci)

codegenRuby_all
  :: RubyTarget
  -> [(Name, SDecl)]
  -> [FilePath]
  -> [String]
  -> FilePath
  -> OutputType
  -> IO ()
codegenRuby_all target definitions includes libs filename outputType = do
  let bytecode = map toBC definitions
  let info = initCompileInfo bytecode
  let rb = concatMap (translateDecl info) bytecode
  let full = concatMap processFunction rb
  let code = deadCodeElim full
  let (cons, opt) = optimizeConstructors code
  let (header, rt) = case target of
                          Ruby -> ("", "")

  included   <- concat <$> getIncludes includes
  path       <- (++) <$> getDataDir <*> (pure "/rbrts/")
  idrRuntime <- readFile $ path ++ "Runtime-common.rb"
  -- tgtRuntime <- readFile $ concat [path, "Runtime", rt, ".rb"]
  let runtime = (  header
                ++ includeLibs libs
                ++ included
                ++ idrRuntime
                -- ++ tgtRuntime
                )
  TIO.writeFile filename (  T.pack runtime
                         `T.append` T.concat (map compileRuby opt)
                         `T.append` T.concat (map compileRuby cons)
                         `T.append` main
                         `T.append` invokeMain
                         )
  setPermissions filename (emptyPermissions { readable   = True
                                            , executable = False
                                            , writable   = True
                                            })
    where
      deadCodeElim :: [Ruby] -> [Ruby]
      deadCodeElim rb = concatMap collectFunctions rb
        where
          collectFunctions :: Ruby -> [Ruby]
          collectFunctions fun@(RubyAlloc name _)
            | name == translateName (sMN 0 "runMain") = [fun]

          collectFunctions fun@(RubyAlloc name (Just (RubyFunction _ body))) =
            let invokations = sum $ map (
                    \x -> execState (countInvokations name x) 0
                  ) rb
             in if invokations == 0
                   then []
                   else [fun]

          countInvokations :: String -> Ruby -> State Int ()
          countInvokations name (RubyAlloc _ (Just (RubyFunction _ body))) =
            countInvokations name body

          countInvokations name (RubySeq seq) =
            void $ traverse (countInvokations name) seq

          countInvokations name (RubyAssign _ rhs) =
            countInvokations name rhs

          countInvokations name (RubyCond conds) =
            void $ traverse (
                runKleisli $ arr id *** Kleisli (countInvokations name)
              ) conds

          countInvokations name (RubySwitch _ conds def) =
            void $ traverse (
              runKleisli $ arr id *** Kleisli (countInvokations name)
            ) conds >> traverse (countInvokations name) def

          countInvokations name (RubyApp lhs rhs) =
            void $ countInvokations name lhs >> traverse (countInvokations name) rhs

          countInvokations name (RubyNew _ args) =
            void $ traverse (countInvokations name) args

          countInvokations name (RubyArray args) =
            void $ traverse (countInvokations name) args

          countInvokations name (RubyIdent name')
            | name == name' = get >>= put . (+1)
            | otherwise     = return ()

          countInvokations _ _ = return ()

      processFunction :: Ruby -> [Ruby]
      processFunction =
        collectSplitFunctions . (\x -> evalRWS (splitFunction x) () 0)

      includeLibs :: [String] -> String
      includeLibs =
        concatMap (\lib -> "var " ++ lib ++ " = require(\"" ++ lib ++"\");\n")

      getIncludes :: [FilePath] -> IO [String]
      getIncludes = mapM readFile

      main :: T.Text
      main =
        compileRuby $ RubyAlloc "main" (Just $
          RubyFunction [] (
            case target of
                 Ruby -> mainFun
          )
        )

      mainFun :: Ruby
      mainFun =
        RubySeq [ RubyAlloc "vm" (Just $ RubyNew "I_VM" [])
              , RubyApp (RubyIdent "i_SCHED") [RubyIdent "vm"]
              , RubyApp (
                  RubyIdent (translateName (sMN 0 "runMain") ++ ".call")
                ) [RubyNum (RubyInt 0)]
              , RubyWhile (RubyProj rbCALLSTACK "length > 0") (
                  RubySeq [ RubyAlloc "func" (Just rbPOP)
                        , RubyAlloc "args" (Just rbPOP)
                        , RubyApp (RubyProj (RubyIdent "func") "call") [RubyIdent "*args"]
                        ]
                )
              ]

      invokeMain :: T.Text
      invokeMain = compileRuby $ RubyApp (RubyIdent "main.call") []

optimizeConstructors :: [Ruby] -> ([Ruby], [Ruby])
optimizeConstructors rb =
    let (rb', cons) = runState (traverse optimizeConstructor' rb) M.empty in
        (map (allocCon . snd) (M.toList cons), rb')
  where
    allocCon :: (String, Ruby) -> Ruby
    allocCon (name, con) = RubyAlloc name (Just con)

    newConstructor :: Int -> String
    newConstructor n = "$i_CON_" ++ show n

    optimizeConstructor' :: Ruby -> State (M.Map Int (String, Ruby)) Ruby
    optimizeConstructor' rb@(RubyNew "I_CON" [ RubyNum (RubyInt tag)
                                           , RubyArray []
                                           , a
                                           , e
                                           ]) = do
      s <- get
      case M.lookup tag s of
           Just (i, c) -> return $ RubyIdent i
           Nothing     -> do let n = newConstructor tag
                             put $ M.insert tag (n, rb) s
                             return $ RubyIdent n

    optimizeConstructor' (RubySeq seq) =
      RubySeq <$> traverse optimizeConstructor' seq

    optimizeConstructor' (RubySwitch reg cond def) = do
      cond' <- traverse (runKleisli $ arr id *** Kleisli optimizeConstructor') cond
      def'  <- traverse optimizeConstructor' def
      return $ RubySwitch reg cond' def'

    optimizeConstructor' (RubyCond cond) =
      RubyCond <$> traverse (runKleisli $ arr id *** Kleisli optimizeConstructor') cond

    optimizeConstructor' (RubyAlloc fun (Just (RubyFunction args body))) = do
      body' <- optimizeConstructor' body
      return $ RubyAlloc fun (Just (RubyFunction args body'))

    optimizeConstructor' (RubyAssign lhs rhs) = do
      lhs' <- optimizeConstructor' lhs
      rhs' <- optimizeConstructor' rhs
      return $ RubyAssign lhs' rhs'

    optimizeConstructor' rb = return rb

collectSplitFunctions :: (Ruby, [(Int,Ruby)]) -> [Ruby]
collectSplitFunctions (fun, splits) = map generateSplitFunction splits ++ [fun]
  where
    generateSplitFunction :: (Int,Ruby) -> Ruby
    generateSplitFunction (depth, RubyAlloc name fun) =
      RubyAlloc (name ++ "_" ++ show depth) fun

splitFunction :: Ruby -> RWS () [(Int,Ruby)] Int Ruby
splitFunction (RubyAlloc name (Just (RubyFunction args body@(RubySeq _)))) = do
  body' <- splitSequence body
  return $ RubyAlloc name (Just (RubyFunction args body'))
    where
      splitCondition :: Ruby -> RWS () [(Int,Ruby)] Int Ruby
      splitCondition rb
        | RubyCond branches <- rb =
            RubyCond <$> processBranches branches
        | RubySwitch cond branches def <- rb =
            RubySwitch cond <$> (processBranches branches) <*> (traverse splitSequence def)
        | otherwise = return rb
        where
          processBranches :: [(Ruby,Ruby)] -> RWS () [(Int,Ruby)] Int [(Ruby,Ruby)]
          processBranches =
            traverse (runKleisli (arr id *** Kleisli splitSequence))

      splitSequence :: Ruby -> RWS () [(Int, Ruby)] Int Ruby
      splitSequence rb@(RubySeq seq) =
        let (pre,post) = break isCall seq in
            case post of
                 []                    -> RubySeq <$> traverse splitCondition seq
                 [rb@(RubyCond _)]       -> splitCondition rb
                 [rb@(RubySwitch {})] -> splitCondition rb
                 [_]                   -> return rb
                 (call:rest) -> do
                   depth <- get
                   put (depth + 1)
                   new <- splitFunction (newFun rest)
                   tell [(depth, new)]
                   return $ RubySeq (pre ++ (newCall depth : [call]))

      splitSequence rb = return rb

      isCall :: Ruby -> Bool
      isCall (RubyApp (RubyIdent "i_CALL") _) = True
      isCall _                            = False

      newCall :: Int -> Ruby
      newCall depth =
        RubyApp (RubyIdent "i_CALL") [ RubyIdent $ name ++ "_" ++ show depth
                                 , RubyArray [rbOLDBASE, rbMYOLDBASE]
                                 ]

      newFun :: [Ruby] -> Ruby
      newFun seq =
        RubyAlloc name (Just $ RubyFunction ["oldbase", "myoldbase"] (RubySeq seq))

splitFunction rb = return rb

translateDecl :: CompileInfo -> (Name, [BC]) -> [Ruby]
translateDecl info (name@(MN 0 fun), bc)
  | txt "APPLY" == fun =
         allocCaseFunctions (snd body)
      ++ [ RubyAlloc (
               translateName name
           ) (Just $ RubyFunction ["oldbase"] (
               RubySeq $ RubyAlloc "myoldbase" (Just . RubyNum $ RubyInt 0) : map (translateBC info) (fst body) ++ [
                 RubyCond [ ( (translateReg $ caseReg (snd body)) `rbInstanceOf` "I_CON" `rbAnd` (RubyProj (translateReg $ caseReg (snd body)) "app")
                          , RubyApp (RubyProj (translateReg $ caseReg (snd body)) "app.call") [rbOLDBASE, rbMYOLDBASE]
                          )
                          , ( RubyNoop
                            , RubySeq $ map (translateBC info) (defaultCase (snd body))
                            )
                        ]
               ]
             )
           )
         ]

  | txt "EVAL" == fun =
         allocCaseFunctions (snd body)
      ++ [ RubyAlloc (
               translateName name
           ) (Just $ RubyFunction ["oldbase"] (
               RubySeq $ RubyAlloc "myoldbase" Nothing : map (translateBC info) (fst body) ++ [
                 RubyCond [ ( (translateReg $ caseReg (snd body)) `rbInstanceOf` "I_CON" `rbAnd` (RubyProj (translateReg $ caseReg (snd body)) "ev")
                          , RubyApp (RubyProj (translateReg $ caseReg (snd body)) "ev.call") [rbOLDBASE, rbMYOLDBASE]
                          )
                          , ( RubyNoop
                            , RubySeq $ map (translateBC info) (defaultCase (snd body))
                            )
                        ]
               ]
             )
           )
         ]
  where
    body :: ([BC], [BC])
    body = break isCase bc

    isCase :: BC -> Bool
    isCase bc
      | CASE {} <- bc = True
      | otherwise          = False

    defaultCase :: [BC] -> [BC]
    defaultCase ((CASE _ _ _ (Just d)):_) = d

    caseReg :: [BC] -> Reg
    caseReg ((CASE _ r _ _):_) = r

    allocCaseFunctions :: [BC] -> [Ruby]
    allocCaseFunctions ((CASE _ _ c _):_) = splitBranches c
    allocCaseFunctions _                  = []

    splitBranches :: [(Int, [BC])] -> [Ruby]
    splitBranches = map prepBranch

    prepBranch :: (Int, [BC]) -> Ruby
    prepBranch (tag, code) =
      RubyAlloc (
        translateName name ++ "_" ++ show tag
      ) (Just $ RubyFunction ["oldbase", "myoldbase"] (
          RubySeq $ map (translateBC info) code
        )
      )

translateDecl info (name, bc) =
  [ RubyAlloc (
       translateName name
     ) (Just $ RubyFunction ["oldbase"] (
         RubySeq $ RubyAlloc "myoldbase" (Just . RubyNum $ RubyInt 0) : map (translateBC info)bc
       )
     )
  ]


translateReg :: Reg -> Ruby
translateReg reg
  | RVal <- reg = rbRET
  | Tmp  <- reg = RubyRaw "//TMPREG"
  | L n  <- reg = rbLOC n
  | T n  <- reg = rbTOP n

translateConstant :: Const -> Ruby
translateConstant (I i)                    = RubyNum (RubyInt i)
translateConstant (Fl f)                   = RubyNum (RubyFloat f)
translateConstant (Ch c)                   = RubyString $ translateChar c
translateConstant (Str s)                  = RubyString $ concatMap translateChar s
translateConstant (AType (ATInt ITNative)) = RubyType RubyIntTy
translateConstant StrType                  = RubyType RubyStringTy
translateConstant (AType (ATInt ITBig))    = RubyType RubyIntegerTy
translateConstant (AType ATFloat)          = RubyType RubyFloatTy
translateConstant (AType (ATInt ITChar))   = RubyType RubyCharTy
translateConstant PtrType                  = RubyType RubyPtrTy
translateConstant Forgot                   = RubyType RubyForgotTy
translateConstant (BI 0)                   = RubyNum (RubyInt 0)
translateConstant (BI 1)                   = RubyNum (RubyInt 1)
translateConstant (BI i)                   = RubyNum $ RubyInteger (RubyBigInt i)
translateConstant (B8 b)                   = RubyWord (RubyWord8 b)
translateConstant (B16 b)                  = RubyWord (RubyWord16 b)
translateConstant (B32 b)                  = RubyWord (RubyWord32 b)
translateConstant (B64 b)                  = RubyWord (RubyWord64 b)
translateConstant c =
  RubyError $ "Unimplemented Constant: " ++ show c


translateChar :: Char -> String
translateChar ch
  | '\a'   <- ch       = "\\u0007"
  | '\b'   <- ch       = "\\b"
  | '\f'   <- ch       = "\\f"
  | '\n'   <- ch       = "\\n"
  | '\r'   <- ch       = "\\r"
  | '\t'   <- ch       = "\\t"
  | '\v'   <- ch       = "\\v"
  | '\SO'  <- ch       = "\\u000E"
  | '\DEL' <- ch       = "\\u007F"
  | '\\'   <- ch       = "\\\\"
  | '\"'   <- ch       = "\\\""
  | '\''   <- ch       = "\\\'"
  | ch `elem` asciiTab = "\\u00" ++ fill (showHex (ord ch) "")
  | otherwise          = [ch]
  where
    fill :: String -> String
    fill s = if length s == 1
                then '0' : s
                else s

    asciiTab =
      ['\NUL', '\SOH', '\STX', '\ETX', '\EOT', '\ENQ', '\ACK', '\BEL',
       '\BS',  '\HT',  '\LF',  '\VT',  '\FF',  '\CR',  '\SO',  '\SI',
       '\DLE', '\DC1', '\DC2', '\DC3', '\DC4', '\NAK', '\SYN', '\ETB',
       '\CAN', '\EM',  '\SUB', '\ESC', '\FS',  '\GS',  '\RS',  '\US']

translateName :: Name -> String
translateName n = "$_idris_" ++ concatMap cchar (showCG n)
  where cchar x | isAlphaNum x = [x]
                | otherwise    = "_" ++ show (fromEnum x) ++ "_"

rbASSIGN :: CompileInfo -> Reg -> Reg -> Ruby
rbASSIGN _ r1 r2 = RubyAssign (translateReg r1) (translateReg r2)

rbASSIGNCONST :: CompileInfo -> Reg -> Const -> Ruby
rbASSIGNCONST _ r c = RubyAssign (translateReg r) (translateConstant c)

rbCALL :: CompileInfo -> Name -> Ruby
rbCALL _ n =
  RubyApp (
    RubyIdent "i_CALL"
  ) [RubyIdent (translateName n), RubyArray [rbMYOLDBASE]]

rbTAILCALL :: CompileInfo -> Name -> Ruby
rbTAILCALL _ n =
  RubyApp (
    RubyIdent "i_CALL"
  ) [RubyIdent (translateName n), RubyArray [rbOLDBASE]]

rbFOREIGN :: CompileInfo -> Reg -> String -> [(FType, Reg)] -> Ruby
rbFOREIGN _ reg n args
  | n == "putStr"
  , [(FString, arg)] <- args =
      RubyAssign (
        translateReg reg
      ) (
        RubyApp (RubyIdent "puts") [translateReg arg]
      )

  | n == "isNull"
  , [(FPtr, arg)] <- args =
      RubyAssign (
        translateReg reg
      ) (
        RubyBinOp "==" (translateReg arg) RubyNull
      )

  | n == "idris_eqPtr"
  , [(_, lhs),(_, rhs)] <- args =
      RubyAssign (
        translateReg reg
      ) (
        RubyBinOp "==" (translateReg lhs) (translateReg rhs)
      )
  | otherwise =
     RubyAssign (
       translateReg reg
     ) (
       RubyFFI n (map generateWrapper args)
     )
    where
      generateWrapper :: (FType, Reg) -> Ruby
      generateWrapper (ty, reg)
        | FFunction _ _ <- ty =
            RubyApp (RubyIdent "i_ffiWrap") [ translateReg reg
                                        , RubyIdent "oldbase"
                                        , RubyIdent "myoldbase"
                                        ]
        | FFunctionIO <- ty =
            RubyApp (RubyIdent "i_ffiWrap") [ translateReg reg
                                        , RubyIdent "oldbase"
                                        , RubyIdent "myoldbase"
                                        ]

      generateWrapper (_, reg) =
        translateReg reg

rbREBASE :: CompileInfo -> Ruby
rbREBASE _ = RubyAssign rbSTACKBASE rbOLDBASE

rbSTOREOLD :: CompileInfo ->Ruby
rbSTOREOLD _ = RubyAssign rbMYOLDBASE rbSTACKBASE

rbADDTOP :: CompileInfo -> Int -> Ruby
rbADDTOP info n
  | 0 <- n    = RubyNoop
  | otherwise =
      RubyBinOp "+=" rbSTACKTOP (RubyNum (RubyInt n))

rbTOPBASE :: CompileInfo -> Int -> Ruby
rbTOPBASE _ 0  = RubyAssign rbSTACKTOP rbSTACKBASE
rbTOPBASE _ n  = RubyAssign rbSTACKTOP (RubyBinOp "+" rbSTACKBASE (RubyNum (RubyInt n)))


rbBASETOP :: CompileInfo -> Int -> Ruby
rbBASETOP _ 0 = RubyAssign rbSTACKBASE rbSTACKTOP
rbBASETOP _ n = RubyAssign rbSTACKBASE (RubyBinOp "+" rbSTACKTOP (RubyNum (RubyInt n)))

rbNULL :: CompileInfo -> Reg -> Ruby
rbNULL _ r = RubyAssign (translateReg r) RubyNull

rbERROR :: CompileInfo -> String -> Ruby
rbERROR _ = RubyError

rbSLIDE :: CompileInfo -> Int -> Ruby
rbSLIDE _ 1 = RubyAssign (rbLOC 0) (rbTOP 0)
rbSLIDE _ n = RubyApp (RubyIdent "i_SLIDE") [RubyNum (RubyInt n)]

rbMKCON :: CompileInfo -> Reg -> Int -> [Reg] -> Ruby
rbMKCON info r t rs =
  RubyAssign (translateReg r) (
    RubyNew "I_CON" [ RubyNum (RubyInt t)
                  , RubyArray (map translateReg rs)
                  , if t `elem` compileInfoApplyCases info
                       then RubyIdent $ translateName (sMN 0 "APPLY") ++ "_" ++ show t
                       else RubyNull
                  , if t `elem` compileInfoEvalCases info
                       then RubyIdent $ translateName (sMN 0 "EVAL") ++ "_" ++ show t
                       else RubyNull
                  ]
  )

rbCASE :: CompileInfo -> Bool -> Reg -> [(Int, [BC])] -> Maybe [BC] -> Ruby
rbCASE info safe reg cases def =
  RubySwitch (tag safe $ translateReg reg) (
    map ((RubyNum . RubyInt) *** prepBranch) cases
  ) (fmap prepBranch def)
    where
      tag :: Bool -> Ruby -> Ruby
      tag True  = rbCTAG
      tag False = rbTAG

      prepBranch :: [BC] -> Ruby
      prepBranch bc = RubySeq $ map (translateBC info) bc

      rbTAG :: Ruby -> Ruby
      rbTAG rb =
        (RubyTernary (rb `rbInstanceOf` "I_CON") (
          RubyProj rb "tag"
        ) (RubyNum (RubyInt $ negate 1)))

      rbCTAG :: Ruby -> Ruby
      rbCTAG rb = RubyProj rb "tag"


rbCONSTCASE :: CompileInfo -> Reg -> [(Const, [BC])] -> Maybe [BC] -> Ruby
rbCONSTCASE info reg cases def =
  RubyCond $ (
    map (rbEq (translateReg reg) . translateConstant *** prepBranch) cases
  ) ++ (maybe [] ((:[]) . ((,) RubyNoop) . prepBranch) def)
    where
      prepBranch :: [BC] -> Ruby
      prepBranch bc = RubySeq $ map (translateBC info) bc

rbPROJECT :: CompileInfo -> Reg -> Int -> Int -> Ruby
rbPROJECT _ reg loc 0  = RubyNoop
rbPROJECT _ reg loc 1  =
  RubyAssign (rbLOC loc) (
    RubyIndex (
      RubyProj (translateReg reg) "args"
    ) (
      RubyNum (RubyInt 0)
    )
  )
rbPROJECT _ reg loc ar =
  RubyApp (RubyIdent "i_PROJECT") [ translateReg reg
                              , RubyNum (RubyInt loc)
                              , RubyNum (RubyInt ar)
                              ]

rbOP :: CompileInfo -> Reg -> PrimFn -> [Reg] -> Ruby
rbOP _ reg op args = RubyAssign (translateReg reg) rbOP'
  where
    rbOP' :: Ruby
    rbOP'
      | LNoOp <- op = translateReg (last args)

      | (LZExt (ITFixed IT8) ITNative)  <- op = rbUnPackBits $ translateReg (last args)
      | (LZExt (ITFixed IT16) ITNative) <- op = rbUnPackBits $ translateReg (last args)
      | (LZExt (ITFixed IT32) ITNative) <- op = rbUnPackBits $ translateReg (last args)
      | (LZExt (ITFixed IT64) ITNative) <- op = rbUnPackBits $ translateReg (last args)

      | (LZExt _ ITBig)        <- op = rbUnPackBits $ translateReg (last args)
      | (LPlus (ATInt ITBig))  <- op
      , (lhs:rhs:_)            <- args = translateBinaryOp "+" lhs rhs
      | (LMinus (ATInt ITBig)) <- op
      , (lhs:rhs:_)            <- args = translateBinaryOp "-" lhs rhs
      | (LTimes (ATInt ITBig)) <- op
      , (lhs:rhs:_)            <- args = translateBinaryOp "*" lhs rhs
      | (LSDiv (ATInt ITBig))  <- op
      , (lhs:rhs:_)            <- args = translateBinaryOp "/" lhs rhs
      | (LSRem (ATInt ITBig))  <- op
      , (lhs:rhs:_)            <- args = translateBinaryOp "%" lhs rhs
      | (LEq (ATInt ITBig))    <- op
      , (lhs:rhs:_)            <- args = translateBinaryOp "==" lhs rhs
      | (LSLt (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = translateBinaryOp "<" lhs rhs
      | (LSLe (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = translateBinaryOp "<=" lhs rhs
      | (LSGt (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = translateBinaryOp ">" lhs rhs
      | (LSGe (ATInt ITBig))   <- op
      , (lhs:rhs:_)            <- args = translateBinaryOp ">=" lhs rhs

      | (LPlus ATFloat)  <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "+" lhs rhs
      | (LMinus ATFloat) <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "-" lhs rhs
      | (LTimes ATFloat) <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "*" lhs rhs
      | (LSDiv ATFloat)  <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "/" lhs rhs
      | (LEq ATFloat)    <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "==" lhs rhs
      | (LSLt ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "<" lhs rhs
      | (LSLe ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp "<=" lhs rhs
      | (LSGt ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp ">" lhs rhs
      | (LSGe ATFloat)   <- op
      , (lhs:rhs:_)      <- args = translateBinaryOp ">=" lhs rhs

      | (LPlus (ATInt ITChar)) <- op
      , (lhs:rhs:_)            <- args =
          rbCall "i_fromCharCode" [
            RubyBinOp "+" (
              rbCall "i_charCode" [translateReg lhs]
            ) (
              rbCall "i_charCode" [translateReg rhs]
            )
          ]

      | (LTrunc (ITFixed IT16) (ITFixed IT8)) <- op
      , (arg:_)                               <- args =
          rbPackUBits8 (
            RubyBinOp "&" (rbUnPackBits $ translateReg arg) (RubyNum (RubyInt 0xFF))
          )

      | (LTrunc (ITFixed IT32) (ITFixed IT16)) <- op
      , (arg:_)                                <- args =
          rbPackUBits16 (
            RubyBinOp "&" (rbUnPackBits $ translateReg arg) (RubyNum (RubyInt 0xFFFF))
          )

      | (LTrunc (ITFixed IT64) (ITFixed IT32)) <- op
      , (arg:_)                                <- args =
          rbPackUBits32 (
            RubyBinOp "&" (rbUnPackBits $ translateReg arg) (RubyNum (RubyInt 0xFFFFFFFF))
          )

      | (LTrunc ITBig (ITFixed IT64)) <- op
      , (arg:_)                       <- args =
          rbPackUBits64 (
            RubyBinOp "&" (rbUnPackBits $ translateReg arg) (RubyNum $ RubyInteger (RubyBigInt 0xFFFFFFFFFFFFFFFF))
          )

      | (LLSHR (ITFixed IT8)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits8 (
            RubyBinOp ">>" (rbUnPackBits $ translateReg lhs) (rbUnPackBits $ translateReg rhs)
          )

      | (LLSHR (ITFixed IT16)) <- op
      , (lhs:rhs:_)            <- args =
          rbPackUBits16 (
            RubyBinOp ">>" (rbUnPackBits $ translateReg lhs) (rbUnPackBits $ translateReg rhs)
          )

      | (LLSHR (ITFixed IT32)) <- op
      , (lhs:rhs:_)            <- args =
          rbPackUBits32  (
            RubyBinOp ">>" (rbUnPackBits $ translateReg lhs) (rbUnPackBits $ translateReg rhs)
          )

      | (LLSHR (ITFixed IT64)) <- op
      , (lhs:rhs:_)            <- args =
          rbPackUBits64  (
            RubyBinOp ">>" (rbUnPackBits $ translateReg lhs) (rbUnPackBits $ translateReg rhs)
          )

      | (LSHL (ITFixed IT8)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits8 (
            RubyBinOp "<<" (rbUnPackBits $ translateReg lhs) (rbUnPackBits $ translateReg rhs)
          )

      | (LSHL (ITFixed IT16)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits16 (
            RubyBinOp "<<" (rbUnPackBits $ translateReg lhs) (rbUnPackBits $ translateReg rhs)
          )

      | (LSHL (ITFixed IT32)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits32  (
            RubyBinOp "<<" (rbUnPackBits $ translateReg lhs) (rbUnPackBits $ translateReg rhs)
          )

      | (LSHL (ITFixed IT64)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits64  (
            RubyBinOp "<<" (rbUnPackBits $ translateReg lhs) (rbUnPackBits $ translateReg rhs)
          )

      | (LAnd (ITFixed IT8)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits8 (
            RubyBinOp "&" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LAnd (ITFixed IT16)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits16 (
            RubyBinOp "&" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LAnd (ITFixed IT32)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits32 (
            RubyBinOp "&" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LAnd (ITFixed IT64)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits64 (
            RubyBinOp "&" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LOr (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args =
          rbPackUBits8 (
            RubyBinOp "|" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LOr (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits16 (
            RubyBinOp "|" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LOr (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits32 (
            RubyBinOp "|" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LOr (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits64 (
            RubyBinOp "|" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LXOr (ITFixed IT8)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits8 (
            RubyBinOp "^" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LXOr (ITFixed IT16)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits16 (
            RubyBinOp "^" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LXOr (ITFixed IT32)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits32 (
            RubyBinOp "^" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LXOr (ITFixed IT64)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits64 (
            RubyBinOp "^" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LPlus (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                   <- args =
          rbPackUBits8 (
            RubyBinOp "+" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LPlus (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackUBits16 (
            RubyBinOp "+" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LPlus (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackUBits32 (
            RubyBinOp "+" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LPlus (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackUBits64 (
            RubyBinOp "+" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LMinus (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackUBits8 (
            RubyBinOp "-" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LMinus (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                     <- args =
          rbPackUBits16 (
            RubyBinOp "-" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LMinus (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                     <- args =
          rbPackUBits32 (
            RubyBinOp "-" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LMinus (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                     <- args =
          rbPackUBits64 (
            RubyBinOp "-" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LTimes (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackUBits8 (
            RubyBinOp "*" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LTimes (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                     <- args =
          rbPackUBits16 (
            RubyBinOp "*" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LTimes (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                     <- args =
          rbPackUBits32 (
            RubyBinOp "*" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LTimes (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                     <- args =
          rbPackUBits64 (
            RubyBinOp "*" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LEq (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                 <- args =
          rbPackUBits8 (
            RubyBinOp "==" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LEq (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                  <- args =
          rbPackUBits16 (
            RubyBinOp "==" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LEq (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                  <- args =
          rbPackUBits32 (
            RubyBinOp "==" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LEq (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                   <- args =
          rbPackUBits64 (
            RubyBinOp "==" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LLt (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args =
          rbPackUBits8 (
            RubyBinOp "<" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LLt (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits16 (
            RubyBinOp "<" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LLt (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits32 (
            RubyBinOp "<" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LLt (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits64 (
            RubyBinOp "<" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LLe (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args =
          rbPackUBits8 (
            RubyBinOp "<=" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LLe (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits16 (
            RubyBinOp "<=" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LLe (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits32 (
            RubyBinOp "<=" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LLe (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits64 (
            RubyBinOp "<=" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LGt (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args =
          rbPackUBits8 (
            RubyBinOp ">" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LGt (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits16 (
            RubyBinOp ">" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )
      | (LGt (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits32 (
            RubyBinOp ">" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LGt (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits64 (
            RubyBinOp ">" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LGe (ITFixed IT8)) <- op
      , (lhs:rhs:_)         <- args =
          rbPackUBits8 (
            RubyBinOp ">=" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LGe (ITFixed IT16)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits16 (
            RubyBinOp ">=" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )
      | (LGe (ITFixed IT32)) <- op
      , (lhs:rhs:_)          <- args =
          rbPackUBits32 (
            RubyBinOp ">=" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LGe (ITFixed IT64)) <- op
      , (lhs:rhs:_)          <- args = 
          rbPackUBits64 (
            RubyBinOp ">=" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LUDiv (ITFixed IT8)) <- op
      , (lhs:rhs:_)           <- args =
          rbPackUBits8 (
            RubyBinOp "/" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LUDiv (ITFixed IT16)) <- op
      , (lhs:rhs:_)            <- args =
          rbPackUBits16 (
            RubyBinOp "/" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LUDiv (ITFixed IT32)) <- op
      , (lhs:rhs:_)            <- args =
          rbPackUBits32 (
            RubyBinOp "/" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LUDiv (ITFixed IT64)) <- op
      , (lhs:rhs:_)            <- args =
          rbPackUBits64 (
            RubyBinOp "/" (rbUnPackBits (translateReg lhs)) (rbUnPackBits (translateReg rhs))
          )

      | (LSDiv (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                   <- args =
          rbPackSBits8 (
            RubyBinOp "/" (
              rbUnPackBits $ rbPackSBits8 $ rbUnPackBits (translateReg lhs)
            ) (
              rbUnPackBits $ rbPackSBits8 $ rbUnPackBits (translateReg rhs)
            )
          )

      | (LSDiv (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackSBits16 (
            RubyBinOp "/" (
              rbUnPackBits $ rbPackSBits16 $ rbUnPackBits (translateReg lhs)
            ) (
              rbUnPackBits $ rbPackSBits16 $ rbUnPackBits (translateReg rhs)
            )
          )

      | (LSDiv (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackSBits32 (
            RubyBinOp "/" (
              rbUnPackBits $ rbPackSBits32 $ rbUnPackBits (translateReg lhs)
            ) (
              rbUnPackBits $ rbPackSBits32 $ rbUnPackBits (translateReg rhs)
            )
          )

      | (LSDiv (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackSBits64 (
            RubyBinOp "/" (
              rbUnPackBits $ rbPackSBits32 $ rbUnPackBits (translateReg lhs)
            ) (
              rbUnPackBits $ rbPackSBits32 $ rbUnPackBits (translateReg rhs)
            )
          )

      | (LSRem (ATInt (ITFixed IT8))) <- op
      , (lhs:rhs:_)                   <- args =
          rbPackSBits8 (
            RubyBinOp "%" (
              rbUnPackBits $ rbPackSBits8 $ rbUnPackBits (translateReg lhs)
            ) (
              rbUnPackBits $ rbPackSBits8 $ rbUnPackBits (translateReg rhs)
            )
          )

      | (LSRem (ATInt (ITFixed IT16))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackSBits16 (
            RubyBinOp "%" (
              rbUnPackBits $ rbPackSBits16 $ rbUnPackBits (translateReg lhs)
            ) (
              rbUnPackBits $ rbPackSBits16 $ rbUnPackBits (translateReg rhs)
            )
          )

      | (LSRem (ATInt (ITFixed IT32))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackSBits32 (
            RubyBinOp "%" (
              rbUnPackBits $ rbPackSBits32 $ rbUnPackBits (translateReg lhs)
            ) (
              rbUnPackBits $ rbPackSBits32 $ rbUnPackBits (translateReg rhs)
            )
          )

      | (LSRem (ATInt (ITFixed IT64))) <- op
      , (lhs:rhs:_)                    <- args =
          rbPackSBits64 (
            RubyBinOp "%" (
              rbUnPackBits $ rbPackSBits32 $ rbUnPackBits (translateReg lhs)
            ) (
              rbUnPackBits $ rbPackSBits32 $ rbUnPackBits (translateReg rhs)
            )
          )

      | (LCompl (ITFixed IT8)) <- op
      , (arg:_)                <- args =
          rbPackSBits8 $ RubyPreOp "~" $ rbUnPackBits (translateReg arg)

      | (LCompl (ITFixed IT16)) <- op
      , (arg:_)                 <- args =
          rbPackSBits16 $ RubyPreOp "~" $ rbUnPackBits (translateReg arg)

      | (LCompl (ITFixed IT32)) <- op
      , (arg:_)                 <- args =
          rbPackSBits32 $ RubyPreOp "~" $ rbUnPackBits (translateReg arg)

      | (LCompl (ITFixed IT64)) <- op
      , (arg:_)     <- args =
          rbPackSBits64 $ RubyPreOp "~" $ rbUnPackBits (translateReg arg)

      | (LPlus _)   <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "+" lhs rhs
      | (LMinus _)  <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "-" lhs rhs
      | (LTimes _)  <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "*" lhs rhs
      | (LSDiv _)   <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "/" lhs rhs
      | (LSRem _)   <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "%" lhs rhs
      | (LEq _)     <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "==" lhs rhs
      | (LSLt _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "<" lhs rhs
      | (LSLe _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "<=" lhs rhs
      | (LSGt _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp ">" lhs rhs
      | (LSGe _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp ">=" lhs rhs
      | (LAnd _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "&" lhs rhs
      | (LOr _)     <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "|" lhs rhs
      | (LXOr _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "^" lhs rhs
      | (LSHL _)    <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "<<" rhs lhs
      | (LASHR _)   <- op
      , (lhs:rhs:_) <- args = translateBinaryOp ">>" rhs lhs
      | (LCompl _)  <- op
      , (arg:_)     <- args = RubyPreOp "~" (translateReg arg)

      | LStrConcat  <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "+" lhs rhs
      | LStrEq      <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "==" lhs rhs
      | LStrLt      <- op
      , (lhs:rhs:_) <- args = translateBinaryOp "<" lhs rhs
      | LStrLen     <- op
      , (arg:_)     <- args = RubyProj (translateReg arg) "length"
      | (LStrInt ITNative)      <- op
      , (arg:_)                 <- args = rbMeth (translateReg arg) "to_i" []
      | (LIntStr ITNative)      <- op
      , (arg:_)                 <- args = rbMeth (translateReg arg) "to_s" []
      | (LSExt ITNative ITBig)  <- op
      , (arg:_)                 <- args = rbMeth (translateReg arg) "to_s" []
      | (LTrunc ITBig ITNative) <- op
      , (arg:_)                 <- args = rbMeth (translateReg arg) "to_i" []
      | (LIntStr ITBig)         <- op
      , (arg:_)                 <- args = rbMeth (translateReg arg) "to_s" []
      | (LStrInt ITBig)         <- op
      , (arg:_)                 <- args = rbMeth (translateReg arg) "to_i" []
      | LFloatStr               <- op
      , (arg:_)                 <- args = rbMeth (translateReg arg) "to_s" []
      | LStrFloat               <- op
      , (arg:_)                 <- args = rbMeth (translateReg arg) "to_f" []
      | (LIntFloat ITNative)    <- op
      , (arg:_)                 <- args = translateReg arg
      | (LFloatInt ITNative)    <- op
      , (arg:_)                 <- args = translateReg arg
      | (LChInt ITNative)       <- op
      , (arg:_)                 <- args = rbCall "i_charCode" [translateReg arg]
      | (LIntCh ITNative)       <- op
      , (arg:_)                 <- args = rbCall "i_fromCharCode" [translateReg arg]

      | LFExp       <- op
      , (arg:_)     <- args = rbCall "Math.exp" [translateReg arg]
      | LFLog       <- op
      , (arg:_)     <- args = rbCall "Math.log" [translateReg arg]
      | LFSin       <- op
      , (arg:_)     <- args = rbCall "Math.sin" [translateReg arg]
      | LFCos       <- op
      , (arg:_)     <- args = rbCall "Math.cos" [translateReg arg]
      | LFTan       <- op
      , (arg:_)     <- args = rbCall "Math.tan" [translateReg arg]
      | LFASin      <- op
      , (arg:_)     <- args = rbCall "Math.asin" [translateReg arg]
      | LFACos      <- op
      , (arg:_)     <- args = rbCall "Math.acos" [translateReg arg]
      | LFATan      <- op
      , (arg:_)     <- args = rbCall "Math.atan" [translateReg arg]
      | LFSqrt      <- op
      , (arg:_)     <- args = rbCall "Math.sqrt" [translateReg arg]
      | LFFloor     <- op
      , (arg:_)     <- args = rbCall "Math.floor" [translateReg arg]
      | LFCeil      <- op
      , (arg:_)     <- args = rbCall "Math.ceil" [translateReg arg]

      | LStrCons    <- op
      , (lhs:rhs:_) <- args = invokeMeth lhs "concat" [rhs]
      | LStrHead    <- op
      , (arg:_)     <- args = RubyIndex (translateReg arg) (RubyNum (RubyInt 0))
      | LStrRev     <- op
      , (arg:_)     <- args = RubyProj (translateReg arg) "split('').reverse().join('')"
      | LStrIndex   <- op
      , (lhs:rhs:_) <- args = RubyIndex (translateReg lhs) (translateReg rhs)
      | LStrTail    <- op
      , (arg:_)     <- args =
          let v = translateReg arg in
              RubyApp (RubyProj v "substr") [
                RubyNum (RubyInt 1),
                RubyBinOp "-" (RubyProj v "length") (RubyNum (RubyInt 1))
              ]

      | LSystemInfo <- op
      , (arg:_) <- args = rbCall "i_systemInfo"  [translateReg arg]
      | LNullPtr    <- op
      , (_)         <- args = RubyNull
      | otherwise = RubyError $ "Not implemented: " ++ show op
        where
          translateBinaryOp :: String -> Reg -> Reg -> Ruby
          translateBinaryOp op lhs rhs =
            RubyBinOp op (translateReg lhs) (translateReg rhs)

          invokeMeth :: Reg -> String -> [Reg] -> Ruby
          invokeMeth obj meth args =
            RubyApp (RubyProj (translateReg obj) meth) $ map translateReg args


rbRESERVE :: CompileInfo -> Int -> Ruby
rbRESERVE _ _ = RubyNoop

rbSTACK :: Ruby
rbSTACK = RubyIdent "$i_valstack"

rbCALLSTACK :: Ruby
rbCALLSTACK = RubyIdent "$i_callstack"

rbSTACKBASE :: Ruby
rbSTACKBASE = RubyIdent "$i_valstack_base"

rbSTACKTOP :: Ruby
rbSTACKTOP = RubyIdent "$i_valstack_top"

rbOLDBASE :: Ruby
rbOLDBASE = RubyIdent "oldbase"

rbMYOLDBASE :: Ruby
rbMYOLDBASE = RubyIdent "myoldbase"

rbRET :: Ruby
rbRET = RubyIdent "$i_ret"

rbLOC :: Int -> Ruby
rbLOC 0 = RubyIndex rbSTACK rbSTACKBASE
rbLOC n = RubyIndex rbSTACK (RubyBinOp "+" rbSTACKBASE (RubyNum (RubyInt n)))

rbTOP :: Int -> Ruby
rbTOP 0 = RubyIndex rbSTACK rbSTACKTOP
rbTOP n = RubyIndex rbSTACK (RubyBinOp "+" rbSTACKTOP (RubyNum (RubyInt n)))

rbPUSH :: [Ruby] -> Ruby
rbPUSH args = RubyApp (RubyProj rbCALLSTACK "push") args

rbPOP :: Ruby
rbPOP = RubyApp (RubyProj rbCALLSTACK "pop") []

translateBC :: CompileInfo -> BC -> Ruby
translateBC info bc
  | ASSIGN r1 r2          <- bc = rbASSIGN info r1 r2
  | ASSIGNCONST r c       <- bc = rbASSIGNCONST info r c
  | UPDATE r1 r2          <- bc = rbASSIGN info r1 r2
  | ADDTOP n              <- bc = rbADDTOP info n
  | NULL r                <- bc = rbNULL info r
  | CALL n                <- bc = rbCALL info n
  | TAILCALL n            <- bc = rbTAILCALL info n
  | FOREIGNCALL r _ _ n a <- bc = rbFOREIGN info r n a
  | TOPBASE n             <- bc = rbTOPBASE info n
  | BASETOP n             <- bc = rbBASETOP info n
  | STOREOLD              <- bc = rbSTOREOLD info
  | SLIDE n               <- bc = rbSLIDE info n
  | REBASE                <- bc = rbREBASE info
  | RESERVE n             <- bc = rbRESERVE info n
  | MKCON r t rs          <- bc = rbMKCON info r t rs
  | CASE s r c d          <- bc = rbCASE info s r c d
  | CONSTCASE r c d       <- bc = rbCONSTCASE info r c d
  | PROJECT r l a         <- bc = rbPROJECT info r l a
  | OP r o a              <- bc = rbOP info r o a
  | ERROR e               <- bc = rbERROR info e
  | otherwise                   = RubyRaw $ "//" ++ show bc


{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
module IRTS.Ruby.AST where

import Data.Word
import Data.Char (isDigit)

import qualified Data.Text as T

data RubyType = RubyIntTy
            | RubyStringTy
            | RubyIntegerTy
            | RubyFloatTy
            | RubyCharTy
            | RubyPtrTy
            | RubyForgotTy
            deriving Eq


data RubyInteger = RubyBigZero
               | RubyBigOne
               | RubyBigInt Integer
               | RubyBigIntExpr Ruby
               deriving Eq


data RubyNum = RubyInt Int
           | RubyFloat Double
           | RubyInteger RubyInteger
           deriving Eq


data RubyWord = RubyWord8 Word8
            | RubyWord16 Word16
            | RubyWord32 Word32
            | RubyWord64 Word64
            deriving Eq


data RubyAnnotation = RubyConstructor deriving Eq


instance Show RubyAnnotation where
  show RubyConstructor = "class"


data Ruby = RubyRaw String
        | RubyIdent String
        | RubyFunction [String] Ruby
        | RubyType RubyType
        | RubySeq [Ruby]
        | RubyReturn Ruby
        | RubyApp Ruby [Ruby]
        | RubyNew String [Ruby]
        | RubyError String
        | RubyBinOp String Ruby Ruby
        | RubyPreOp String Ruby
        | RubyPostOp String Ruby
        | RubyProj Ruby String
        | RubyNull
        | RubyUndefined
        | RubyThis
        | RubyTrue
        | RubyFalse
        | RubyArray [Ruby]
        | RubyString String
        | RubyNum RubyNum
        | RubyWord RubyWord
        | RubyAssign Ruby Ruby
        | RubyAlloc String (Maybe Ruby)
        | RubyIndex Ruby Ruby
        | RubySwitch Ruby [(Ruby, Ruby)] (Maybe Ruby)
        | RubyCond [(Ruby, Ruby)]
        | RubyTernary Ruby Ruby Ruby
        | RubyParens Ruby
        | RubyWhile Ruby Ruby
        | RubyFFI String [Ruby]
        | RubyAnnotation RubyAnnotation Ruby
        | RubyNoop
        deriving Eq


data FFI = FFICode Char | FFIArg Int | FFIError String

ffi :: String -> [String] -> T.Text
ffi code args = let parsed = ffiParse code in
                    case ffiError parsed of
                         Just err -> error err
                         Nothing  -> renderFFI parsed args
  where
    ffiParse :: String -> [FFI]
    ffiParse ""           = []
    ffiParse ['%']        = [FFIError $ "FFI - Invalid positional argument"]
    ffiParse ('%':'%':ss) = FFICode '%' : ffiParse ss
    ffiParse ('%':s:ss)
      | isDigit s =
         FFIArg (
           read $ s : takeWhile isDigit ss
          ) : ffiParse (dropWhile isDigit ss)
      | otherwise =
          [FFIError "FFI - Invalid positional argument"]
    ffiParse (s:ss) = FFICode s : ffiParse ss


    ffiError :: [FFI] -> Maybe String
    ffiError []                 = Nothing
    ffiError ((FFIError s):xs)  = Just s
    ffiError (x:xs)             = ffiError xs


    renderFFI :: [FFI] -> [String] -> T.Text
    renderFFI [] _ = ""
    renderFFI (FFICode c : fs) args = c `T.cons` renderFFI fs args
    renderFFI (FFIArg i : fs) args
      | i < length args && i >= 0 =
            T.pack (args !! i)
          `T.append` renderFFI fs args
      | otherwise = error "FFI - Argument index out of bounds"

compileRuby :: Ruby -> T.Text
compileRuby = compileRuby' 0

compileRuby' :: Int -> Ruby -> T.Text
compileRuby' indent RubyNoop = ""

compileRuby' indent (RubyAnnotation annotation rb) =
   ""
  `T.append` T.pack (show annotation)
  `T.append` " */\n"
  `T.append` compileRuby' indent rb

compileRuby' indent (RubyFFI raw args) =
  ffi raw (map (T.unpack . compileRuby' indent) args)

compileRuby' indent (RubyRaw code) =
  T.pack code

compileRuby' indent (RubyIdent ident) =
  T.pack ident

compileRuby' indent (RubyFunction args body) =
   T.replicate indent " " `T.append` "|"
   `T.append` T.intercalate "," (map T.pack args)
   `T.append` "|\n"
   `T.append` compileRuby' (indent + 2) body
   `T.append` "\nend\n"

compileRuby' indent (RubyType ty)
  | RubyIntTy     <- ty = "i_Int"
  | RubyStringTy  <- ty = "i_String"
  | RubyIntegerTy <- ty = "i_Integer"
  | RubyFloatTy   <- ty = "i_Float"
  | RubyCharTy    <- ty = "i_Char"
  | RubyPtrTy     <- ty = "i_Ptr"
  | RubyForgotTy  <- ty = "i_Forgot"

compileRuby' indent (RubySeq seq) =
  T.intercalate "\n" (
    map (
      (T.replicate indent " " `T.append`) . (compileRuby' indent)
    ) $ filter (/= RubyNoop) seq
  ) `T.append` ""

compileRuby' indent (RubyReturn val) =
  "return " `T.append` compileRuby' indent val

compileRuby' indent (RubyApp lhs rhs)
  | RubyFunction {} <- lhs =
    T.concat ["(", compileRuby' indent lhs, ")(", args, ")"]
  | otherwise =
    T.concat [compileRuby' indent lhs, "(", args, ")"]
  where args :: T.Text
        args = T.intercalate "," $ map (compileRuby' 0) rhs

compileRuby' indent (RubyNew name args) =
  T.pack name
  `T.append` ".new"
  `T.append` "("
  `T.append` T.intercalate "," (map (compileRuby' 0) args)
  `T.append` ")"

compileRuby' indent (RubyError exc) =
  "(function(){throw new Error(\"" `T.append` T.pack exc `T.append` "\")})()"

compileRuby' indent (RubyBinOp op lhs rhs) =
    compileRuby' indent lhs
  `T.append` " "
  `T.append` T.pack op
  `T.append` " "
  `T.append` compileRuby' indent rhs

compileRuby' indent (RubyPreOp op val) =
  T.pack op `T.append` compileRuby' indent val

compileRuby' indent (RubyProj obj field)
  | RubyFunction {} <- obj =
    T.concat ["(", compileRuby' indent obj, ").", T.pack field]
  | RubyAssign {} <- obj =
    T.concat ["(", compileRuby' indent obj, ").", T.pack field]
  | otherwise =
    compileRuby' indent obj `T.append` ('.' `T.cons` T.pack field)

compileRuby' indent RubyNull =
  "nil"

compileRuby' indent RubyUndefined =
  "undefined"

compileRuby' indent RubyThis =
  "self"

compileRuby' indent RubyTrue =
  "true"

compileRuby' indent RubyFalse =
  "false"

compileRuby' indent (RubyArray elems) =
  "[" `T.append` T.intercalate "," (map (compileRuby' 0) elems) `T.append` "]"

compileRuby' indent (RubyString str) =
  "\"" `T.append` T.pack str `T.append` "\""

compileRuby' indent (RubyNum num)
  | RubyInt i                    <- num = T.pack (show i)
  | RubyFloat f                  <- num = T.pack (show f)
  | RubyInteger RubyBigZero        <- num = T.pack "0"
  | RubyInteger RubyBigOne         <- num = T.pack "1"
  | RubyInteger (RubyBigInt i)     <- num = T.pack (show i)
  | RubyInteger (RubyBigIntExpr e) <- num = compileRuby' indent e

compileRuby' indent (RubyAssign lhs rhs) =
  compileRuby' indent lhs `T.append` " = " `T.append` compileRuby' indent rhs

compileRuby' 0 (RubyAlloc name (Just val@(RubyNew _ _))) =
  T.pack name
  `T.append` " = "
  `T.append` compileRuby' 0 val
  `T.append` "\n"

compileRuby' indent (RubyAlloc name val) =
    let expr = maybe "" (compileRuby' indent) val
    in case val of (Nothing)               -> ""
                   (Just (RubyFunction _ _)) -> T.pack name `T.append` " = Proc.new do " `T.append`  expr                   
                   (_)                     -> T.pack name `T.append` " = " `T.append` expr

compileRuby' indent (RubyIndex lhs rhs) =
    compileRuby' indent lhs
  `T.append` "["
  `T.append` compileRuby' indent rhs
  `T.append` "]"

compileRuby' indent (RubyCond branches) = createIfBlock branches
  where    
    createIfBlock [] =
      createEndExpr

    createIfBlock [(RubyNoop,RubyNoop)] =
      createIfBlock []

    createIfBlock [(cond,e)] =
      createIfExpr cond e `T.append`
      createIfBlock []

    createIfBlock ((RubyNoop,RubyNoop):(RubyNoop,e):[]) =
      createElseExpr e `T.append`
      createIfBlock []
    
    createIfBlock ((RubyNoop,RubyNoop):(cond,e):branches) =
      createElseIfExpr cond e `T.append`
      createIfBlock ((RubyNoop,RubyNoop):branches)

    createIfBlock ((cond, expr):branches) =
      createIfExpr cond expr `T.append`
      createIfBlock ((RubyNoop,RubyNoop):branches)

    createExpr e@(RubySeq _) = compileRuby' (indent + 2) e
    createExpr e = T.replicate (indent + 2) " " `T.append` compileRuby' 0 e

    createIfExpr' stmt cond e = 
      stmt `T.append` " " `T.append` compileRuby' indent cond `T.append`"\n"
          `T.append` createExpr e

    createIfExpr cond e = createIfExpr' "if" cond e `T.append` "\n"

    createElseIfExpr cond e = T.replicate indent " " `T.append` 
                              createIfExpr' "elsif" cond e `T.append` "\n"

    createElseExpr e = T.replicate indent " " `T.append` 
                       "else\n" `T.append` createExpr e
    
    createEndExpr = "\n" `T.append` T.replicate indent " " `T.append` "end"

compileRuby' indent (RubySwitch val [(_,RubySeq seq)] Nothing) =
  let (h,t) = splitAt 1 seq in
         (T.concat (map (compileRuby' indent) h) `T.append` ";\n")
      `T.append` (
        T.intercalate ";\n" $ map (
          (T.replicate indent " " `T.append`) . compileRuby' indent
        ) t
      )

compileRuby' indent (RubySwitch val branches def) =
     "case " `T.append` compileRuby' indent val `T.append` "\n"
  `T.append` T.concat (map mkBranch branches)
  `T.append` mkDefault def
  `T.append` T.replicate indent " " `T.append` "end"
  where
    mkBranch :: (Ruby, Ruby) -> T.Text
    mkBranch (tag, code) =
         T.replicate (indent + 2) " "
      `T.append` "when "
      `T.append` compileRuby' indent tag
      `T.append` "\n"
      `T.append` compileRuby' (indent + 4) code
      `T.append` "\n"
      `T.append` (T.replicate (indent + 4) " " `T.append` "\n")

    mkDefault :: Maybe Ruby -> T.Text
    mkDefault Nothing = ""
    mkDefault (Just def) =
         T.replicate (indent + 2) " " `T.append` "else\n"
      `T.append` compileRuby' (indent + 4)def
      `T.append` "\n"


compileRuby' indent (RubyTernary cond true false) =
  let c = compileRuby' indent cond
      t = compileRuby' indent true
      f = compileRuby' indent false in
        "("
      `T.append` c
      `T.append` ")?("
      `T.append` t
      `T.append` "):("
      `T.append` f
      `T.append` ")"

compileRuby' indent (RubyParens rb) =
  "(" `T.append` compileRuby' indent rb `T.append` ")"

compileRuby' indent (RubyWhile cond body) =
     "while " `T.append` compileRuby' indent cond `T.append` " do\n"
  `T.append` compileRuby' (indent + 2) body
  `T.append` "\n" `T.append` T.replicate indent " " `T.append` "end"

compileRuby' indent (RubyWord word)
  | RubyWord8  b <- word =
      "new Uint8Array([" `T.append` T.pack (show b) `T.append` "])"
  | RubyWord16 b <- word =
      "new Uint16Array([" `T.append` T.pack (show b) `T.append` "])"
  | RubyWord32 b <- word =
      "new Uint32Array([" `T.append` T.pack (show b) `T.append` "])"
  | RubyWord64 b <- word = T.pack (show b)

rbInstanceOf :: Ruby -> String -> Ruby
rbInstanceOf obj cls = rbMeth obj "instance_of?" [(RubyIdent cls)]

rbOr :: Ruby -> Ruby -> Ruby
rbOr lhs rhs = RubyBinOp "||" lhs rhs

rbAnd :: Ruby -> Ruby -> Ruby
rbAnd lhs rhs = RubyBinOp "&&" lhs rhs

rbMeth :: Ruby -> String -> [Ruby] -> Ruby
rbMeth obj meth args = RubyApp (RubyProj obj meth) args

rbCall :: String -> [Ruby] -> Ruby
rbCall fun args = RubyApp (RubyIdent fun) args

rbTypeOf :: Ruby -> Ruby
rbTypeOf rb = RubyPreOp ".is_a? " rb

rbEq :: Ruby -> Ruby -> Ruby
rbEq lhs@(RubyNum (RubyInteger _)) rhs = RubyApp (RubyProj lhs "equals") [rhs]
rbEq lhs rhs@(RubyNum (RubyInteger _)) = RubyApp (RubyProj lhs "equals") [rhs]
rbEq lhs rhs = RubyBinOp "==" lhs rhs

rbNotEq :: Ruby -> Ruby -> Ruby
rbNotEq lhs rhs = RubyBinOp "!=" lhs rhs

rbIsNumber :: Ruby -> Ruby
rbIsNumber rb = (rbTypeOf rb) `rbEq` (RubyString "number")

rbIsNull :: Ruby -> Ruby
rbIsNull rb = RubyBinOp "==" rb RubyNull

rbBigInt :: Ruby -> Ruby
rbBigInt (RubyString "0") = RubyNum (RubyInteger RubyBigZero)
rbBigInt (RubyString "1") = RubyNum (RubyInteger RubyBigOne)
rbBigInt rb               = RubyNum $ RubyInteger $ RubyBigIntExpr rb

rbUnPackBits :: Ruby -> Ruby
rbUnPackBits rb = RubyIndex rb $ RubyNum (RubyInt 0)

rbPackUBits8 :: Ruby -> Ruby
-- rbPackUBits8 rb = RubyNew "Uint8Array" [RubyArray [rb]]
rbPackUBits8 rb = rbMeth (RubyArray [rb]) "pack" [(RubyString "C*")]

rbPackUBits16 :: Ruby -> Ruby
-- rbPackUBits16 rb = RubyNew "Uint16Array" [RubyArray [rb]]
rbPackUBits16 rb = rbMeth (RubyArray [rb]) "pack" [(RubyString "L*")]

rbPackUBits32 :: Ruby -> Ruby
-- rbPackUBits32 rb = RubyNew "Uint32Array" [RubyArray [rb]]
rbPackUBits32 rb = rbMeth (RubyArray [rb]) "pack" [(RubyString "C*")]

rbPackUBits64 :: Ruby -> Ruby
rbPackUBits64 rb = rbMeth (RubyArray [rb]) "pack" [(RubyString "Q*")]

rbPackSBits8 :: Ruby -> Ruby
rbPackSBits8 rb = RubyNew "Int8Array" [RubyArray [rb]]

rbPackSBits16 :: Ruby -> Ruby
rbPackSBits16 rb = RubyNew "Int16Array" [RubyArray [rb]]

rbPackSBits32 :: Ruby -> Ruby
rbPackSBits32 rb = RubyNew "Int32Array" [RubyArray [rb]]


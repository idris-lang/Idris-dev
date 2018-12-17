{-|
Module      : IRTS.JavaScript.AST
Description : The JavaScript AST.

License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE DeriveDataTypeable, OverloadedStrings, PatternGuards #-}

module IRTS.JavaScript.AST
  ( JsExpr(..)
  , JsStmt(..)
  , jsAst2Text
  , jsStmt2Text
  , jsLazy
  , jsCurryLam
  , jsCurryApp
  , jsAppN
  , jsExpr2Stmt
  , jsStmt2Expr
  , jsSetVar
  ) where

import Data.Char
import Data.Data
import Data.Text (Text)
import qualified Data.Text as T
import Numeric

data JsStmt
  = JsEmpty
  | JsComment Text
  | JsExprStmt JsExpr
  | JsFun Text
          [Text]
          JsStmt
  | JsSeq JsStmt
          JsStmt
  | JsReturn JsExpr
  | JsDecVar Text
             JsExpr
  | JsDecConst Text
               JsExpr
  | JsDecLet Text
             JsExpr
  | JsSet JsExpr
          JsExpr
  | JsIf JsExpr
         JsStmt
         (Maybe JsStmt)
  | JsSwitchCase JsExpr
                 [(JsExpr, JsStmt)]
                 (Maybe JsStmt)
  | JsError JsExpr
  | JsForever JsStmt
  | JsContinue
  | JsBreak
  deriving (Show, Eq, Data, Typeable)

data JsExpr
  = JsNull
  | JsUndefined
  | JsThis
  | JsLambda [Text]
             JsStmt
  | JsApp JsExpr
          [JsExpr]
  | JsNew JsExpr
          [JsExpr]
  | JsPart JsExpr
           Text
  | JsMethod JsExpr
             Text
             [JsExpr]
  | JsVar Text
  | JsArrayProj JsExpr
                JsExpr
  | JsObj [(Text, JsExpr)]
  | JsProp JsExpr
           Text
  | JsInt Int
  | JsBool Bool
  | JsInteger Integer
  | JsDouble Double
  | JsStr String
  | JsArray [JsExpr]
  | JsErrorExp JsExpr
  | JsUniOp Text
            JsExpr
  | JsBinOp Text
            JsExpr
            JsExpr
  | JsForeign Text
              [JsExpr]
  | JsB2I JsExpr
  | JsForce JsExpr
  deriving (Show, Eq, Data, Typeable)

translateChar :: Char -> String
translateChar ch
  | '\b'   <- ch       = "\\b"
  | '\f'   <- ch       = "\\f"
  | '\n'   <- ch       = "\\n"
  | '\r'   <- ch       = "\\r"
  | '\t'   <- ch       = "\\t"
  | '\v'   <- ch       = "\\v"
  | '\\'   <- ch       = "\\\\"
  | '\"'   <- ch       = "\\\""
  | '\''   <- ch       = "\\\'"
  | ord ch < 0x20      = "\\x" ++ pad 2 (showHex (ord ch) "")
  | ord ch < 0x7f      = [ch]  -- 0x7f '\DEL'
  | ord ch <= 0xff     = "\\x" ++ pad 2 (showHex (ord ch) "")
  | ord ch <= 0xffff   = "\\u" ++ pad 4 (showHex (ord ch) "")
  | ord ch <= 0x10ffff = "\\u{" ++ showHex (ord ch) "}"
  | otherwise          = error $ "Invalid Unicode code point U+" ++ showHex (ord ch) ""
  where
    pad :: Int -> String -> String
    pad n s = replicate (n - length s) '0' ++ s

indent :: Text -> Text
indent x =
  let l = T.lines x
      il = map (\y -> T.replicate 4 " " `T.append` y) l
  in T.unlines il

jsCurryLam :: [Text] -> JsExpr -> JsExpr
jsCurryLam [] body = body
jsCurryLam (x:xs) body = JsLambda [x] $ JsReturn $ jsCurryLam xs body

jsCurryApp :: JsExpr -> [JsExpr] -> JsExpr
jsCurryApp fn [] = fn
jsCurryApp fn args = foldl (\ff aa -> JsApp ff [aa]) fn args

jsAppN :: Text -> [JsExpr] -> JsExpr
jsAppN fn args = JsApp (JsVar fn) args

jsSetVar :: Text -> JsExpr -> JsStmt
jsSetVar n x = JsSet (JsVar n) x

jsStmt2Text :: JsStmt -> Text
jsStmt2Text JsEmpty = ""
jsStmt2Text (JsComment c) = T.unlines $ map ("// " `T.append`) $ T.lines c
jsStmt2Text (JsExprStmt e) = T.concat [jsAst2Text e, ";"]
jsStmt2Text (JsReturn x) = T.concat ["return ", jsAst2Text x, ";"]
jsStmt2Text (JsDecVar name exp) =
  T.concat ["var ", name, " = ", jsAst2Text exp, ";"]
jsStmt2Text (JsDecConst name exp) =
  T.concat ["const ", name, " = ", jsAst2Text exp, ";"]
jsStmt2Text (JsDecLet name exp) =
  T.concat ["let ", name, " = ", jsAst2Text exp, ";"]
jsStmt2Text (JsFun name args body) =
  T.concat
    [ "function "
    , name
    , "("
    , T.intercalate ", " args
    , "){\n"
    , indent $ jsStmt2Text body
    , "}\n"
    ]
jsStmt2Text (JsIf cond conseq (Just next@(JsIf _ _ _))) =
  T.concat
    [ "if("
    , jsAst2Text cond
    , ") {\n"
    , indent $ jsStmt2Text conseq
    , "} else "
    , jsStmt2Text next
    ]
jsStmt2Text (JsIf cond conseq (Just alt)) =
  T.concat
    [ "if("
    , jsAst2Text cond
    , ") {\n"
    , indent $ jsStmt2Text conseq
    , "} else {\n"
    , indent $ jsStmt2Text alt
    , "}\n"
    ]
jsStmt2Text (JsIf cond conseq Nothing) =
  T.concat ["if(", jsAst2Text cond, ") {\n", indent $ jsStmt2Text conseq, "}\n"]
jsStmt2Text (JsSwitchCase exp l d) =
  T.concat
    [ "switch("
    , jsAst2Text exp
    , "){\n"
    , indent $ T.concat $ map case2Text l
    , indent $ default2Text d
    , "}\n"
    ]
  where
    case2Text :: (JsExpr, JsStmt) -> Text
    case2Text (x, y) =
      T.concat
        [ "case "
        , jsAst2Text x
        , ":\n"
        , indent $ T.concat [jsStmt2Text y, ";\nbreak;\n"]
        ]
    default2Text :: Maybe JsStmt -> Text
    default2Text Nothing = ""
    default2Text (Just z) =
      T.concat ["default:\n", indent $ T.concat [jsStmt2Text z, ";\nbreak;\n"]]
jsStmt2Text (JsError t) = T.concat ["$JSRTS.die(", jsAst2Text t, ");\n"]
jsStmt2Text (JsForever x) =
  T.concat ["for(;;) {\n", indent $ jsStmt2Text x, "}\n"]
jsStmt2Text JsContinue = "continue;"
jsStmt2Text JsBreak = "break;"
jsStmt2Text (JsSeq JsEmpty y) = jsStmt2Text y
jsStmt2Text (JsSeq x JsEmpty) = jsStmt2Text x
jsStmt2Text (JsSeq x y) = T.concat [jsStmt2Text x, "\n", jsStmt2Text y]
jsStmt2Text (JsSet term exp) =
  T.concat [jsAst2Text term, " = ", jsAst2Text exp, ";"]

jsAst2Text :: JsExpr -> Text
jsAst2Text JsNull = "null"
jsAst2Text JsUndefined = "(void 0)"
jsAst2Text JsThis = "this"
jsAst2Text (JsLambda args body) =
  T.concat
    [ "(function"
    , "("
    , T.intercalate ", " args
    , "){\n"
    , indent $ jsStmt2Text body
    , "})"
    ]
jsAst2Text (JsApp fn args) =
  T.concat [jsAst2Text fn, "(", T.intercalate ", " $ map jsAst2Text args, ")"]
jsAst2Text (JsNew fn args) =
  T.concat ["new ", jsAst2Text fn, "(", T.intercalate ", " $ map jsAst2Text args, ")"]
jsAst2Text (JsMethod obj name args) =
  T.concat
    [ jsAst2Text obj
    , "."
    , name
    , "("
    , T.intercalate ", " $ map jsAst2Text args
    , ")"
    ]
jsAst2Text (JsPart obj name) =
  T.concat [jsAst2Text obj, "[", T.pack (show name), "]"]
jsAst2Text (JsVar x) = x
jsAst2Text (JsObj props) =
  T.concat
    [ "({"
    , T.intercalate
        ", "
        (map (\(name, val) -> T.concat [name, ": ", jsAst2Text val]) props)
    , "})"
    ]
jsAst2Text (JsProp object name) = T.concat [jsAst2Text object, ".", name]
jsAst2Text (JsArrayProj i exp) =
  T.concat [jsAst2Text exp, "[", jsAst2Text i, "]"]
jsAst2Text (JsInt i) = T.pack $ show i
jsAst2Text (JsBool True) = T.pack "true"
jsAst2Text (JsBool False) = T.pack "false"
jsAst2Text (JsDouble d) = T.pack $ show d
jsAst2Text (JsInteger i) = T.pack $ show i
jsAst2Text (JsStr s) =   "\"" `T.append` T.pack (concatMap translateChar s) `T.append` "\""
jsAst2Text (JsArray l) =
  T.concat ["[", T.intercalate ", " (map jsAst2Text l), "]"]
jsAst2Text (JsErrorExp t) =
  T.concat ["$JSRTS.throw(new Error(  ", jsAst2Text t, "))"]
jsAst2Text (JsBinOp op a1 a2) =
  T.concat ["(", jsAst2Text a1, " ", op, " ", jsAst2Text a2, ")"]
jsAst2Text (JsUniOp op a) = T.concat ["(", op, jsAst2Text a, ")"]
jsAst2Text (JsForeign code args) =
  let args_repl c i [] = c
      args_repl c i (t:r) =
        args_repl (T.replace ("%" `T.append` T.pack (show i)) (T.concat ["(", t, ")"]) c) (i + 1) r
  in T.concat ["(", args_repl code 0 (map jsAst2Text args), ")"]
jsAst2Text (JsB2I x) = jsAst2Text $ JsBinOp "+" x (JsInt 0)
jsAst2Text (JsForce e) = T.concat ["$JSRTS.force(", jsAst2Text e, ")"]

jsLazy :: JsExpr -> JsExpr
jsLazy e = JsNew (JsProp (JsVar "$JSRTS") "Lazy") [(JsLambda [] $ JsReturn e)]

jsExpr2Stmt :: JsExpr -> JsStmt
jsExpr2Stmt = JsExprStmt

jsStmt2Expr :: JsStmt -> JsExpr
jsStmt2Expr (JsExprStmt x) = x
jsStmt2Expr x = JsApp (JsLambda [] x) []

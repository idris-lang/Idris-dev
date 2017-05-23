{-# LANGUAGE DeriveDataTypeable, OverloadedStrings #-}

module IRTS.JavaScript.JsAST
  ( JsExpr(..)
  , JsStmt(..)
  , jsAst2Text
  , jsStmt2Text
  , jsLazy
  , jsCurryLam
  , jsCurryApp
  , jsAppN
  , js_aux_defs
  , jsExpr2Stmt
  , jsStmt2Expr
  ) where

import Data.Data
import Data.Text (Text)
import qualified Data.Text as T

data JsStmt
  = JsEmpty
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
  | JsStr Text
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
  | JsComment Text
  | JsForce JsExpr
  deriving (Show, Eq, Data, Typeable)

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

jsStmt2Text :: JsStmt -> Text
jsStmt2Text JsEmpty = ""
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
jsStmt2Text (JsError t) = T.concat ["throw new Error(  ", jsAst2Text t, ");"]
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
jsAst2Text (JsStr s) = T.pack $ show s
jsAst2Text (JsArray l) =
  T.concat ["[", T.intercalate ", " (map jsAst2Text l), "]"]
jsAst2Text (JsErrorExp t) =
  T.concat ["js_idris_throw2(new Error(  ", jsAst2Text t, "))"]
jsAst2Text (JsBinOp op a1 a2) =
  T.concat ["(", jsAst2Text a1, " ", op, " ", jsAst2Text a2, ")"]
jsAst2Text (JsUniOp op a) = T.concat ["(", op, jsAst2Text a, ")"]
jsAst2Text (JsForeign code args) =
  let args_repl c i [] = c
      args_repl c i (t:r) =
        args_repl (T.replace ("%" `T.append` T.pack (show i)) t c) (i + 1) r
  in T.concat ["(", args_repl code 0 (map jsAst2Text args), ")"]
jsAst2Text (JsB2I x) = jsAst2Text $ JsBinOp "+" x (JsInt 0)
jsAst2Text (JsComment c) = T.concat ["/*", c, "*/"]
jsAst2Text (JsForce e) = T.concat ["js_idris_force(", jsAst2Text e, ")"]

jsLazy :: JsExpr -> JsExpr
jsLazy e = JsObj [("js_idris_lazy_calc", (JsLambda [] $ JsReturn e))]

throw2 =
  T.concat ["var js_idris_throw2 = function (x){\n", " throw x;\n", "}\n"]

force =
  T.concat
    [ "var js_idris_force = function (x){\n"
    , " if(x.js_idris_lazy_calc === undefined){\n"
    , "  return x\n"
    , " }else{\n"
    , "  if(x.js_idris_lazy_val === undefined){\n"
    , "   x.js_idris_lazy_val = x.js_idris_lazy_calc()\n"
    , "  }\n"
    , " return x.js_idris_lazy_val\n"
    , " }\n"
    , "}\n"
    ]

js_aux_defs = T.concat [throw2, force]

jsExpr2Stmt :: JsExpr -> JsStmt
jsExpr2Stmt = JsExprStmt

jsStmt2Expr :: JsStmt -> JsExpr
jsStmt2Expr (JsExprStmt x) = x
jsStmt2Expr x = JsApp (JsLambda [] x) []

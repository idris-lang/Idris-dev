{-|
Module      : IRTS.JavaScript.AST
Description : AST for javascrit
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE DeriveDataTypeable, OverloadedStrings #-}

module IRTS.JavaScript.AST( JsAST(..)
                         , jsAst2Text
                         , js_aux_defs
                         ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Data

data JsAST = JsEmpty
           | JsNull
           | JsLambda [Text] JsAST
           | JsCurryLambda [Text] JsAST
           | JsFun Text [Text] JsAST
--           | JsCurryFun Text [Text] JsAST
           | JsReturn JsAST
           | JsApp Text [JsAST]
           | JsCurryApp JsAST [JsAST]
           | JsMethod JsAST Text [JsAST]
           | JsVar Text
           | JsSeq JsAST JsAST
           | JsConst Text JsAST
           | JsLet Text JsAST
           | JsLetList [(Text, JsAST)]
           | JsSetVar Text JsAST
           | JsArrayProj JsAST JsAST
           | JsInt Int
           | JsInteger Integer
           | JsDouble Double
           | JsStr Text
           | JsArray [JsAST]
           | JsSwitchCase JsAST [(JsAST, JsAST)] (Maybe JsAST)
           | JsError JsAST
           | JsErrorExp JsAST
           | JsBinOp Text JsAST JsAST
           | JsForeign Text [JsAST]
           | JsB2I JsAST
           -- | JsWhileTrue JsAST
           | JsFor (JsAST, JsAST, JsAST) JsAST
           | JsContinue
           | JsBreak
           | JsTrue
           | JsComment Text
           | JsForce JsAST
           | JsLazy JsAST
            deriving (Show, Eq, Data, Typeable)


indent :: Text -> Text
indent x =
  let l  = T.lines x
      il = map (\y -> T.replicate 3 " " `T.append` y) l
  in T.unlines il

curryDef :: [Text] -> JsAST -> Text
curryDef [] body =
  jsAst2Text body
curryDef (x:xs) body =
  T.concat [ "(function", "(", x, "){return "
           , curryDef xs body
           , "})"
           ]


jsAst2Text :: JsAST -> Text
jsAst2Text JsEmpty = ""
jsAst2Text JsNull = "null"
jsAst2Text (JsLambda args body) =
  T.concat [ "(function", "(", T.intercalate ", " args , "){"
           , jsAst2Text body
           , "})"
           ]
jsAst2Text (JsCurryLambda args body) = curryDef args body
jsAst2Text (JsFun name args body) =
  T.concat [ "var ", name, " = function(", T.intercalate ", " args , "){\n"
           , indent $ jsAst2Text body
           , "}\n"
           ]
{-jsAst2Text (JsCurryFun name args body) =
  T.concat [ "var ", name, " = \n"
           , indent $ T.concat [ "(function(){\n"
                               , indent $ curryDef args body
                               , "})()"
                               ]
           ]
-}
jsAst2Text (JsReturn x) = T.concat [ "return ", jsAst2Text x]
jsAst2Text (JsApp fn args) = T.concat [fn, "(", T.intercalate ", " $ map jsAst2Text args, ")"]
jsAst2Text (JsCurryApp fn []) = jsAst2Text fn
jsAst2Text (JsCurryApp fn args) = T.concat [jsAst2Text fn, "(", T.intercalate ")(" $ map jsAst2Text args, ")"]
jsAst2Text (JsMethod obj name args) =
  T.concat [ jsAst2Text obj
           , "."
           , name, "("
           , T.intercalate ", " $ map jsAst2Text args
           , ")"
           ]
jsAst2Text (JsVar x) = x
jsAst2Text (JsSeq JsEmpty y) = jsAst2Text y
jsAst2Text (JsSeq x JsEmpty) = jsAst2Text x
jsAst2Text (JsSeq x y) = T.concat [jsAst2Text x, ";\n", jsAst2Text y]
jsAst2Text (JsConst name exp) = T.concat [ "const ", name, " = ", jsAst2Text exp]
jsAst2Text (JsLet name exp) = T.concat [ "let ", name, " = ", jsAst2Text exp]
jsAst2Text (JsLetList lst) = T.concat [ "let ", T.intercalate ", " (map (\(n,v) -> T.concat [n, " = ", jsAst2Text v]  ) lst) ]
jsAst2Text (JsSetVar name exp) = T.concat [ name, " = ", jsAst2Text exp]
jsAst2Text (JsArrayProj i exp) = T.concat [ jsAst2Text exp, "[", jsAst2Text i, "]"]
jsAst2Text (JsInt i) = T.pack $ show i
jsAst2Text (JsDouble d) = T.pack $ show d
jsAst2Text (JsInteger i) = T.pack $ show i
jsAst2Text (JsStr s) = T.pack $ show s
jsAst2Text (JsArray l) = T.concat [ "[", T.intercalate ", " (map jsAst2Text l), "]"]
jsAst2Text (JsSwitchCase exp l d) =
  T.concat [ "switch(", jsAst2Text exp, "){\n"
           , indent $ T.concat $ map case2Text l
           , indent $ default2Text d
           , "}\n"
           ]
jsAst2Text (JsError t) =
  T.concat ["throw new Error(  ", jsAst2Text t, ")"]
jsAst2Text (JsErrorExp t) =
  T.concat ["js_idris_throw2(new Error(  ", jsAst2Text t, "))"]
jsAst2Text (JsBinOp op a1 a2) =
  T.concat ["(", jsAst2Text a1," ", op, " ",jsAst2Text a2, ")"]
jsAst2Text (JsForeign code args) =
  let args_repl c i [] = c
      args_repl c i (t:r) = args_repl (T.replace ("%" `T.append` T.pack (show i)) t c) (i+1) r
  in T.concat ["(", args_repl code 0 (map jsAst2Text args), ")"]
jsAst2Text (JsB2I x) = jsAst2Text $ JsBinOp "+" x (JsInt 0)
jsAst2Text (JsFor (x,y,z) w) =
  T.concat [ "for(", jsAst2Text x , "; ",jsAst2Text y, "; ",jsAst2Text z,"){\n"
           , indent $ jsAst2Text w
           , "}\n"
           ]
jsAst2Text JsContinue =
  "continue"
jsAst2Text JsBreak =
  "break"
jsAst2Text JsTrue =
  "true"
jsAst2Text (JsComment c)=
  T.concat ["/*",c,"*/"]
jsAst2Text (JsLazy e) =
  T.concat [ "{js_idris_lazy_calc:function(){"
           , indent $ jsAst2Text e
           , "}}"
           ]
jsAst2Text (JsForce e) =
  T.concat ["js_idris_force(", jsAst2Text e, ")"]



case2Text :: (JsAST, JsAST) -> Text
case2Text (x,y) =
  T.concat [ "case ", jsAst2Text x, ":\n"
           , indent $ T.concat [ jsAst2Text y, ";\nbreak;\n"]
           ]

throw2 = T.concat [ "var js_idris_throw2 = function (x){\n"
                  , " throw x;\n"
                  , "}\n\n"
                  ]

force  = T.concat [ "var js_idris_force = function (x){\n"
                  , " if(x === undefined || x.js_idris_lazy_calc === undefined){\n"
                  , "  return x\n"
                  , " }else{\n"
                  , "  if(x.js_idris_lazy_val === undefined){\n"
                  , "   x.js_idris_lazy_val = x.js_idris_lazy_calc()\n"
                  , "  }"
                  , "  return x.js_idris_lazy_val"
                  , "}"
                  , "}\n\n"
                  ]

js_aux_defs = T.concat [throw2, force]

default2Text :: Maybe JsAST -> Text
default2Text Nothing = ""
default2Text (Just z) =
  T.concat [ "default:\n"
           , indent $ T.concat [ jsAst2Text z, ";\nbreak;\n"]
           ]

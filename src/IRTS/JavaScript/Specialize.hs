{-|
Module      : IRTS.JavaScript.Specialize
Description : The JavaScript specializer.

License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE OverloadedStrings, PatternGuards #-}

module IRTS.JavaScript.Specialize
  ( SCtor
  , STest
  , SProj
  , specialCased
  , specialCall
  , qualifyN
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Idris.Core.TT
import IRTS.JavaScript.AST

split :: Char -> String -> [String]
split c "" = [""]
split c (x:xs)
  | c == x = "" : split c xs
  | otherwise =
    let ~(h:t) = split c xs
    in ((x : h) : t)

qualify :: String -> Name -> Name
qualify "" n = n
qualify ns n = sNS n (reverse $ split '.' ns)

qualifyN :: String -> String -> Name
qualifyN ns n = qualify ns $ sUN n

-- special-cased constructors
type SCtor = [JsExpr] -> JsExpr

type STest = JsExpr -> JsExpr

type SProj = JsExpr -> Int -> JsExpr

constructorOptimizeDB :: Map.Map Name (SCtor, STest, SProj)
constructorOptimizeDB =
  Map.fromList
    [ item "Prelude.Bool" "True" (const $ JsBool True) trueTest cantProj
    , item "Prelude.Bool" "False" (const $ JsBool False) falseTest cantProj
    , item "Prelude.Interfaces" "LT" (const $ JsInt (0-1)) ltTest cantProj
    , item "Prelude.Interfaces" "EQ" (const $ JsInt 0) eqTest cantProj
    , item "Prelude.Interfaces" "GT" (const $ JsInt 1) gtTest cantProj
    -- , item "Prelude.List" "::" cons fillList uncons
    -- , item "Prelude.List" "Nil" nil emptyList cantProj
    -- , item "Prelude.Maybe" "Just" (\[x] -> x) notNoneTest justProj
    -- , item "Prelude.Maybe" "Nothing" (const $ JsUndefined) noneTest cantProj
    ]
    -- constructors
  where
    trueTest = id
    falseTest e = JsUniOp (T.pack "!") e
    ltTest e = JsBinOp "<" e (JsInt 0)
    eqTest e = JsBinOp "===" e (JsInt 0)
    gtTest e = JsBinOp ">" e (JsInt 0)
    -- projections
    cantProj x j = error $ "This type should be projected"
    item :: String
         -> String
         -> SCtor
         -> STest
         -> SProj
         -> (Name, (SCtor, STest, SProj))
    item ns n ctor test match = (qualifyN ns n, (ctor, test, match))

specialCased :: Name -> Maybe (SCtor, STest, SProj)
specialCased n = Map.lookup n constructorOptimizeDB

-- special functions
type SSig = (Int, [JsExpr] -> JsExpr)

callSpecializeDB :: Map.Map Name (SSig)
callSpecializeDB =
  Map.fromList
    [ qb "Eq" "Int" "==" "==="
    , qb "Ord" "Int" "<" "<"
    , qb "Ord" "Int" ">" ">"
    , qb "Ord" "Int" "<=" "<="
    , qb "Ord" "Int" ">=" ">="
    , qb "Eq" "Double" "==" "==="
    , qb "Ord" "Double" "<" "<"
    , qb "Ord" "Double" ">" ">"
    , qb "Ord" "Double" "<=" "<="
    , qb "Ord" "Double" ">=" ">="
    ]
  where
    qb intf ty op jsop =
      ( qualify "Prelude.Interfaces" $
        SN $
        WhereN
          0
          (qualify "Prelude.Interfaces" $
           SN $ ImplementationN (qualifyN "Prelude.Interfaces" intf) [ty])
          (SN $ MethodN $ UN op)
      , (2, \[x, y] -> JsBinOp jsop x y))

specialCall :: Name -> Maybe SSig
specialCall n = Map.lookup n callSpecializeDB

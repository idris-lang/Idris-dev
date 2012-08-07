module IRTS.Bytecode where

import IRTS.Lang
import IRTS.Simplified
import Core.TT
import Data.Maybe

-- data Reg = RVal | CaseVar | L Int

-- data BC = ASSIGN Reg Reg
--         | ASSIGNCONST Reg Const
--         | MKCON Reg Int Int
--         | CASE [(Int, [BC])] (Maybe [BC])
--         | GETARGS Int -- discards afterwards
--         | CONSTCASE [(Const, [BC])] (Maybe [BC])
--         | CALL Name
--         | TAILCALL Name
--         | PRINTNUM
--         | PRINTSTR
--         | GROWSTACK Int
--         | DROPSTACK Int
--         | SLIDE Int Int -- number to drop, number to keep
--         | OP PrimFn
--     deriving Show

-- toBC :: (Name, LDecl) -> Maybe (Name, [BC])
-- toBC (n, LConstructor _ _ _) = Nothing
-- toBC (n, LFun n' args exp) = let cleanup = [SLIDE (length args) 1] in
--                                  Just (n, bc (length args - 1) exp cleanup)
-- 
-- bc :: Int -> LExp -> [BC] -> [BC]
-- bc top (LV (Glob n)) c = [CALL n] ++ c
-- bc top (LV (Loc i)) c = [PUSH (top-i)] ++ c
-- bc top (LApp tc fn args) c
--     = bcArgs top args ++
--          if tc then [SLIDE top (length args), TAILCALL fn]
--                else [CALL fn] ++ c
-- bc top (LCon tag _ args) c
--     = bcArgs top args ++ [MKCON tag (length args)] ++ c
-- bc top (LConst i) c = [PUSHCONST i] ++ c
-- bc top (LCase e alts) c = bc top e [] ++
--                            if constCase alts then bcCaseConst top alts
--                                              else bcCase top alts
--                            ++ c
-- bc top (LLet _ v e) c = bc top v [] ++ bc (top + 1) e [] ++ c
-- bc top (LOp prim args) c = bcArgs top args ++ [OP prim] ++ c
-- 
-- bcArgs top [] = []
-- bcArgs top (x : xs) = bc top x [] ++ bcArgs (top + 1) xs
-- 
-- constCase (LConstCase _ _ : _) = True
-- constCase (LConCase _ _ _ _ : _) = False
-- constCase (_ : xs) = constCase xs
-- constCase _ = False
-- 
-- bcCase      top xs = [CASE (mapMaybe (conClause top) xs) (defaultCase top xs)]
-- bcCaseConst top xs = [CONSTCASE (mapMaybe (constClause top) xs) (defaultCase top xs)]
-- 
-- conClause top (LConCase tag _ args e) = Just (tag, GETARGS (length args) :
--                                                bc (top + length args) e []
--                                                   ++ [SLIDE (length args) 1])
-- conClause top _ = Nothing
-- 
-- constClause top (LConstCase c e) = Just (c, bc top e [])
-- constClause top _ = Nothing
-- 
-- defaultCase top [] = Nothing
-- defaultCase top (LDefaultCase e : xs) = Just (bc top e [])
-- defaultCase top (_ : xs) = defaultCase top xs

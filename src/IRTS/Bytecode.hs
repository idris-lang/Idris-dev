module IRTS.Bytecode where

import IRTS.Lang
import Core.TT

data BC = PUSH Int
        | PUSHCONST Const
        | MKCON Int Int
        | CASE [(Int, [BC])] (Maybe [BC])
        | CONSTCASE [(Const, [BC])] (Maybe [BC])
        | PRINTNUM
        | PRINTSTR
        | INTOP PrimFn
    deriving Show

toBC :: (Name, LDecl) -> Maybe (Name, [BC])
toBC (n, LConstructor _ _ _) = Nothing
toBC (n, LFun n' args exp) = Just (n, bc exp)

bc :: LExp -> [BC]
bc x = []

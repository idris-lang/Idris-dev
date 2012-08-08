module IRTS.Bytecode where

import IRTS.Lang
import IRTS.Simplified
import Core.TT
import Data.Maybe

-- TODO: Need L to refer from the bottom of the current stack frame,
-- T from the top.

data Reg = RVal | L Int | T Int
   deriving (Show, Eq)

data BC = ASSIGN Reg Reg
        | ASSIGNCONST Reg Const
        | MKCON Reg Int [Reg]
        | CASE Reg [(Int, [BC])] (Maybe [BC])
        | PROJECT Reg Int Int -- get all args from reg, put them from Int onwards
        | GETARGS Int -- discards afterwards
        | CONSTCASE [(Const, [BC])] (Maybe [BC])
        | CALL Name
        | TAILCALL Name
        | PRINTNUM
        | PRINTSTR
        | GROWSTACK Int
        | DROPSTACK Int
        | SLIDE Int Int -- number to drop, number to keep
        | OP Reg PrimFn [Reg]
    deriving Show

toBC :: (Name, SDecl) -> (Name, [BC])
toBC (n, SFun n' args locs exp) 
   = (n, GROWSTACK locs : bc RVal exp (length args + locs))

clean 0 = []
clean c = [DROPSTACK c]

bc :: Reg -> SExp -> Int -> [BC]
bc reg (SV (Glob n))   c = [CALL n] ++ assign reg RVal ++ clean c
bc reg (SV (Loc i))    c = assign reg (L i) ++ clean c
bc reg (SApp tc f vs)  c 
    = GROWSTACK (length vs) : moveReg (c + length vs) vs
      ++ [CALL f] ++ assign reg RVal ++ clean c
bc reg (SLet (Loc i) e sc) c = bc (L i) e 0 ++ bc reg sc c
bc reg (SCon i _ vs) c = MKCON reg i (map getL vs) : clean c
    where getL (Loc x) = L x
bc reg (SConst i) c = ASSIGNCONST reg i : clean c
bc reg (SOp p vs) c = OP reg p (map getL vs) : clean c
    where getL (Loc x) = L x
bc reg (SCase (Loc l) alts) c 
   | isConst alts = undefined -- constCase reg c l alts
   | otherwise = conCase reg c (L l) alts : clean c

isConst [] = False
isConst (SConstCase _ _ : xs) = True
isConst (SConCase _ _ _ _ _ : xs) = False
isConst (_ : xs) = False

moveReg off [] = []
moveReg off (Loc x : xs) = assign (L off) (L x) ++ moveReg (off + 1) xs

assign r1 r2 | r1 == r2 = []
             | otherwise = [ASSIGN r1 r2]

conCase reg c l xs = CASE l (mapMaybe (caseAlt l reg c) xs)
                                    Nothing

caseAlt l reg c (SConCase lvar tag _ args e)
    = Just (tag, PROJECT l lvar (length args) : bc reg e c) 
caseAlt l reg c _ = Nothing


module IRTS.Bytecode where

-- Bytecode for a stack based VM (e.g. for generating C code with an accurate
-- hand written GC)

import IRTS.Lang
import IRTS.Simplified
import Core.TT
import Data.Maybe

{- We have: 

BASE: Current stack frame's base
TOP:  Top of stack
OLDBASE: Passed in to each function, the previous stack frame's base

L i refers to the stack item at BASE + i
T i refers to the stack item at TOP + i

RVal is a register in which computed values (essentially, what a function
returns) are stored.

-}

data Reg = RVal | L Int | T Int | Tmp
   deriving (Show, Eq)

data BC = ASSIGN Reg Reg
        | ASSIGNCONST Reg Const
        | UPDATE Reg Reg
        | MKCON Reg Int [Reg]
        | CASE Bool -- definitely a constructor, no need to check, if true
               Reg [(Int, [BC])] (Maybe [BC])
        | PROJECT Reg Int Int -- get all args from reg, put them from Int onwards
        | PROJECTINTO Reg Reg Int -- project argument from one reg into another 
        | CONSTCASE Reg [(Const, [BC])] (Maybe [BC])
        | CALL Name
        | TAILCALL Name
        | FOREIGNCALL Reg FLang FType String [(FType, Reg)] 
        | SLIDE Int -- move this number from TOP to BASE 
        | REBASE -- set BASE = OLDBASE
        | RESERVE Int -- reserve n more stack items 
                      -- (i.e. check there's space, grow if necessary)
        | ADDTOP Int -- move the top of stack up
        | TOPBASE Int -- set TOP = BASE + n
        | BASETOP Int -- set BASE = TOP + n
        | STOREOLD -- set OLDBASE = BASE
        | OP Reg PrimFn [Reg]
        | NULL Reg -- clear reg
        | ERROR String
    deriving Show

toBC :: (Name, SDecl) -> (Name, [BC])
toBC (n, SFun n' args locs exp) 
   = (n, reserve locs ++ bc RVal exp True)
  where reserve 0 = []
        reserve n = [RESERVE n, ADDTOP n]

clean True  = [TOPBASE 0, REBASE]
clean False = []

bc :: Reg -> SExp -> Bool -> -- returning
      [BC]
bc reg (SV (Glob n)) r = bc reg (SApp False n []) r
bc reg (SV (Loc i))  r = assign reg (L i) ++ clean r
bc reg (SApp False f vs) r
    = RESERVE (length vs) : moveReg 0 vs
      ++ [STOREOLD, BASETOP 0, ADDTOP (length vs), CALL f] ++ 
         assign reg RVal ++ clean r
bc reg (SApp True f vs) r
    = RESERVE (length vs) : moveReg 0 vs
      ++ [SLIDE (length vs), TOPBASE (length vs), TAILCALL f]
bc reg (SForeign l t fname args) r
    = FOREIGNCALL reg l t fname (map farg args) : clean r
  where farg (ty, Loc i) = (ty, L i)
bc reg (SLet (Loc i) e sc) r = bc (L i) e False ++ bc reg sc r
bc reg (SUpdate (Loc i) sc) r = bc reg sc False ++ [ASSIGN (L i) reg]
                                ++ clean r
bc reg (SCon i _ vs) r = MKCON reg i (map getL vs) : clean r
    where getL (Loc x) = L x
bc reg (SProj (Loc l) i) r = PROJECTINTO reg (L l) i : clean r 
bc reg (SConst i) r = ASSIGNCONST reg i : clean r
bc reg (SOp p vs) r = OP reg p (map getL vs) : clean r
    where getL (Loc x) = L x
bc reg (SError str) r = [ERROR str]
bc reg SNothing r = NULL reg : clean r
bc reg (SCase (Loc l) alts) r 
   | isConst alts = constCase reg (L l) alts r
   | otherwise = conCase True reg (L l) alts r
bc reg (SChkCase (Loc l) alts) r 
   = conCase False reg (L l) alts r

isConst [] = False
isConst (SConstCase _ _ : xs) = True
isConst (SConCase _ _ _ _ _ : xs) = False
isConst (_ : xs) = False

moveReg off [] = []
moveReg off (Loc x : xs) = assign (T off) (L x) ++ moveReg (off + 1) xs

assign r1 r2 | r1 == r2 = []
             | otherwise = [ASSIGN r1 r2]

conCase safe reg l xs r = [CASE safe l (mapMaybe (caseAlt l reg r) xs)
                                (defaultAlt reg xs r)]

constCase reg l xs r = [CONSTCASE l (mapMaybe (constAlt l reg r) xs)
                               (defaultAlt reg xs r)]

caseAlt l reg r (SConCase lvar tag _ args e) 
    = Just (tag, PROJECT l lvar (length args) : bc reg e r) 
caseAlt l reg r _ = Nothing

constAlt l reg r (SConstCase c e) 
    = Just (c, bc reg e r) 
constAlt l reg r _ = Nothing

defaultAlt reg [] r = Nothing
defaultAlt reg (SDefaultCase e : _) r = Just (bc reg e r)
defaultAlt reg (_ : xs) r = defaultAlt reg xs r



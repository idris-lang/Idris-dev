{-|
Module      : IRTS.Bytecode
Description : Bytecode for a stack based VM (e.g. for generating C code with an accurate hand written GC)

Copyright   :
License     : BSD3
Maintainer  : The Idris Community.


BASE: Current stack frame's base
TOP:  Top of stack
OLDBASE: Passed in to each function, the previous stack frame's base

L i refers to the stack item at BASE + i
T i refers to the stack item at TOP + i

RVal is a register in which computed values (essentially, what a function
returns) are stored.

-}
module IRTS.Bytecode where


import Idris.Core.TT
import IRTS.Defunctionalise
import IRTS.Lang
import IRTS.Simplified

import Data.Maybe

data Reg = RVal | L Int | T Int | Tmp
   deriving (Show, Eq)

data BC =
    -- | reg1 = reg2
    ASSIGN Reg Reg

    -- | reg = const
  | ASSIGNCONST Reg Const

    -- | reg1 = reg2 (same as assign, it seems)
  | UPDATE Reg Reg

    -- | reg = constructor, where constructor consists of a tag and
    -- values from registers, e.g. (cons tag args)
    -- the 'Maybe Reg', if set, is a register which can be overwritten
    -- (i.e. safe for mutable update), though this can be ignored
  | MKCON Reg (Maybe Reg) Int [Reg]

    -- | Matching on value of reg: usually (but not always) there are
    -- constructors, hence "Int" for patterns (that's a tag on which
    -- we should match), and the following [BC] is just a list of
    -- instructions for the corresponding case. The last argument is
    -- for default case. When it's not necessary a constructor in the
    -- reg, the Bool should be False, indicating that it's not safe to
    -- work with that as with a constructor, so a check should be
    -- added. If it's not a constructor, default case should be used.
  | CASE Bool
    Reg [(Int, [BC])] (Maybe [BC])

    -- | get a value from register, which should be a constructor, and
    -- put its arguments into the stack, starting from (base + int1)
    -- and onwards; second Int provides arity
  | PROJECT Reg Int Int

    -- | probably not used
  | PROJECTINTO Reg Reg Int -- project argument from one reg into another

    -- | same as CASE, but there's an exact value (not constructor) in reg
  | CONSTCASE Reg [(Const, [BC])] (Maybe [BC])

    -- | just call a function, passing MYOLDBASE (see below) to it
  | CALL Name

    -- | same, perhaps exists just for TCO
  | TAILCALL Name

    -- | set reg to (apply string args),
  | FOREIGNCALL Reg FDesc FDesc [(FDesc, Reg)]

    -- | move this number of elements from TOP to BASE
  | SLIDE Int

    -- | set BASE = OLDBASE
  | REBASE

    -- | reserve n more stack items (i.e. check there's space, grow if
    -- necessary)
  | RESERVE Int

    -- | move the top of stack up
  | ADDTOP Int

    -- | set TOP = BASE + n
  | TOPBASE Int

    -- | set BASE = TOP + n
  | BASETOP Int

    -- | set MYOLDBASE = BASE, where MYOLDBASE is a function-local
    -- variable, set to OLDBASE by default, and passed on function
    -- call to called functions as their OLDBASE
  | STOREOLD

    -- | reg = apply primitive_function args
  | OP Reg PrimFn [Reg]

    -- | clear reg
  | NULL Reg

    -- | throw an error
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
bc reg (SApp False f vs) r =
      if argCount == 0
         then moveReg 0 vs ++ [STOREOLD, BASETOP 0, CALL f] ++ ret
         else RESERVE argCount : moveReg 0 vs ++
            [STOREOLD, BASETOP 0, ADDTOP argCount, CALL f] ++ ret
   where
      ret      = assign reg RVal ++ clean r
      argCount = length vs
bc reg (SApp True f vs) r
    = RESERVE (length vs) : moveReg 0 vs
      ++ [SLIDE (length vs), TOPBASE (length vs), TAILCALL f]
bc reg (SForeign t fname args) r
    = FOREIGNCALL reg t fname (map farg args) : clean r
  where farg (ty, Loc i) = (ty, L i)
bc reg (SLet (Loc i) e sc) r = bc (L i) e False ++ bc reg sc r
bc reg (SUpdate (Loc i) sc) r = bc reg sc False ++ [ASSIGN (L i) reg]
                                ++ clean r
-- bc reg (SUpdate x sc) r = bc reg sc r -- can't update, just do it
bc reg (SCon atloc i _ vs) r
  = MKCON reg (getAllocLoc atloc) i (map getL vs) : clean r
    where getL (Loc x) = L x
          getAllocLoc (Just (Loc x)) = Just (L x)
          getAllocLoc _ = Nothing
bc reg (SProj (Loc l) i) r = PROJECTINTO reg (L l) i : clean r
bc reg (SConst i) r = ASSIGNCONST reg i : clean r
bc reg (SOp p vs) r = OP reg p (map getL vs) : clean r
    where getL (Loc x) = L x
bc reg (SError str) r = [ERROR str]
bc reg SNothing r = NULL reg : clean r
bc reg (SCase up (Loc l) alts) r
   | isConst alts = constCase reg (L l) alts r
   | otherwise = conCase True reg (L l) alts r
bc reg (SChkCase (Loc l) alts) r
   = conCase False reg (L l) alts r
bc reg t r = error $ "Can't compile " ++ show t

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

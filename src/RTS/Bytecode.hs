module RTS.Bytecode where

import Core.TT
import Core.CaseTree
import Core.Evaluate

import Idris.AbsSyntax
import RTS.SC

data SValue = VInt Int
            | VFloat Double
            | VString String
            | VChar Char
            | VBigInt Integer
            | VRef Int
    deriving Show

data BCOp = PUSH SValue
          | SLIDE Int -- Keep top stack value, discard n below it
          | DISCARD Int
          | DISCARDINT Int
          | DISCARDFLOAT Int
          | EVAL Bool
          | MKCON Tag Arity
          | MKTHUNK Name Int Arity
          | MKUNIT
          | CASE [(Int, Bytecode)] (Maybe Bytecode)
          | INTCASE [(Int, Bytecode)] (Maybe Bytecode)
            -- case looks at top stack item, discards immediately,
            -- places constructor args on stack, last to first (first at ref 0)
          | SPLIT -- get arguments from constructor form
          | CALL Name Int -- name, number of arguments to take
          | CALLVAR Int Int  -- stack ref, number of arguments to take
          | FOREIGNCALL String CType [CType] -- TT constants for types 
          | PRIMOP SPrim [Int] -- apply to list of stack references
          | ERROR String
          | DUMP
    deriving Show

type Bytecode = [BCOp]

data BCProg = BCProg [(Name, Bytecode)]
    deriving Show

toSC :: IState -> (Name, Def) -> [(Name, SCDef)]
toSC i (n, d) = case lookup n (idris_scprims i) of
                   Nothing -> sclift (n, d)
                   Just (args, rt, op) -> 
                        let anames = zipWith mkA args [0..] in 
                            [(n, SCDef anames (SPrimOp op (map (SRef . fst) anames)))]
    where mkA t i = (MN i "primArg", t)

bcdefs :: [(Name, SCDef)] -> [(Name, Bytecode)]
bcdefs = map (\ (n, s) -> (n, bc [] s))

class BC a where
    bc :: [(Name, Int)] -> -- local variables + stack offset
          a -> Bytecode

offset :: [(Name, Int)] -> [(Name, Int)]
offset = map (\ (n, i) -> (n, i+1))

-- A bytecode sequence for an expression evaluates that expression and
-- places the result at the top of the stack.

instance BC SCDef where
    bc [] (SCDef args def) = bc (zip (map fst args) [0..]) def 
                                ++ [SLIDE (length args)]

instance BC SCExp where
    bc locs (SRef n) = case lookup n locs of
                                Nothing -> [CALL n 0]
                                Just i  -> [PUSH (VRef i)]
    bc locs (SApp (SRef f) args)
        = bc' locs (reverse args) f
        where bc' locs [] n 
                  = case lookup n locs of
                         Just i -> [CALLVAR i (length args)]
                         Nothing -> [CALL n (length args)]
              bc' locs (x : xs) f = bc locs x ++
                                    bc' (offset locs) xs f
    bc locs (SApp e args)
        = bc locs e ++ bc' (offset locs) (reverse args) ++ [SLIDE 1]
        where bc' locs []  
                  = [CALLVAR (length args) (length args)]
              bc' locs (x : xs) = bc locs x ++
                                  bc' (offset locs) xs
    bc locs (SLet n v sc)
        = bc locs v ++
          bc ((n, 0) : offset locs) sc ++
          [SLIDE 1]

    bc locs (SFCall cname ty args)
        = bc' locs (reverse (map fst args))
        where bc' locs [] = [FOREIGNCALL cname ty (map snd args)]
              bc' locs (x : xs) = bc locs x ++ bc' (offset locs) xs

    bc locs (SCon t args)
        = bc' locs (reverse args)
        where bc' locs [] = [MKCON t (length args)]
              bc' locs (x : xs) = bc locs x ++ bc' (offset locs) xs

    bc locs (SConst (I i)) = [PUSH (VInt i)]
    bc locs (SConst (BI i)) = [PUSH (VBigInt i)]
    bc locs (SConst (Fl f)) = [PUSH (VFloat f)]
    bc locs (SConst (Ch c)) = [PUSH (VChar c)]
    bc locs (SConst (Str s)) = [PUSH (VString s)]
    bc locs (SConst _) = [MKUNIT]

    bc locs (SError str) = [ERROR str]

    bc locs (SCase n alts)
        = let (def, cases, ty) = getCases CASE Nothing [] alts in
              bc locs (SRef n) ++ [ty cases def]
        where getCases ty def cs [] = (def, reverse cs, ty)
              getCases ty _ cs (SDefaultCase e : rest) 
                  = getCases ty (Just (bc locs e)) cs rest
              getCases _ def cs (SConstCase (I c) e : rest)
                  = getCases INTCASE def ((c, bc locs e): cs) rest
              getCases _ def cs (SConCase t ns e : rest)
                  = let locs' = addLocs (reverse ns) locs in
                        getCases CASE def ((t, bc locs' e ++ [SLIDE (length locs')])
                                             : cs) rest
              addLocs [] l = l
              addLocs (n : ns) locs = addLocs ns ((n, 0) : offset locs)

    bc locs (SPrimOp p args)
        = bc' locs (reverse args)
        where bc' locs [] = [PRIMOP p [0..length args-1]]
              bc' locs (x : xs) = bc locs x ++ bc' (offset locs) xs

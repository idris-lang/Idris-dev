module RTS.PreC where

-- A representation close to the code we'll be outputting

import Core.TT

import RTS.Bytecode
import RTS.SC

import Control.Monad.State

data CAtom = CP Name | CL Local | CC Const
   deriving Show

data CExp = CAtom CAtom
          | CApp CAtom [CAtom]
          | CExactApp CAtom [CAtom]
          | CLazy CAtom [CAtom]
          | CFCall String CType [(CAtom, CType)]
          | CPrimOp SPrim [CAtom]
          | CCon Tag [CAtom] 
    deriving Show

data CVal = CTag Local | CIntVal Local
    deriving Show

-- Assignment is to the return value, or some local reference
-- Local reference <n> means <top of stack> - <n>
data Reg = RVal | LVar Local
    deriving Show

data CInst = ASSIGN Reg CExp
           | RESERVE Int
           | CLEAR Int
           | EVAL Local
           | PROJECT Local Local Int
           | SWITCH CVal [(Int, PreC)] PreC
           | ERROR String
           | TAILCALL Int -- number of stack items to clear
                      CAtom [CAtom] 
           | TAILCALLEXACT Int CAtom [CAtom] 
    deriving Show

type PreC = [CInst]

preCdefs :: [(Name, (Int, Bytecode))] -> [(Name, (Int, PreC))]
preCdefs xs = map (\ (n, (i, b)) -> (n, preC xs b)) xs

atom res (BP n) = CP n
atom res (BL n) = CL (res - n)
atom res (BC c) = CC c

preC :: [(Name, (Int, Bytecode))] -> Bytecode -> (Int, PreC)
preC all (BGetArgs ns bc) = (length ns, pc RVal (length ns) bc) 
  where arity n = do (i, b) <- lookup n all
                     return i
        exact (BP n) as = case arity n of
                                Just i -> i == length as
                                Nothing -> False
        exact _ as = False

        pc loc d (BAtom b) = [ASSIGN loc (CAtom (atom d b))]
        pc loc d (BApp f as) 
           | exact f as = [ASSIGN loc (CExactApp (atom d f) (map (atom d) as))]
           | otherwise = [ASSIGN loc (CApp (atom d f) (map (atom d) as))]
        pc loc d (BTailApp f as) 
           | exact f as = [TAILCALLEXACT d (atom d f) (map (atom d) as)]
           | otherwise = [TAILCALL d (atom d f) (map (atom d) as)]
        pc loc d (BLazy f as) = [ASSIGN loc (CLazy (atom d f) (map (atom d) as))]
        pc loc d (BLet x val sc) = pc (LVar (d - x)) d val ++ pc loc d sc 
        pc loc d (BFCall c t args) 
            = [ASSIGN loc (CFCall c t (map (\ (a, ty) -> (atom d a, ty)) args))]
        pc loc d (BCon t args) = [ASSIGN loc (CCon t (map (atom d) args))]
        pc loc d (BPrimOp s args)
            = [ASSIGN loc (CPrimOp s (map (atom d) args))]
        pc loc d (BError s) = [ERROR s]
        pc loc d (BCase l alts)
            = EVAL (d - l) :
              SWITCH (caseTy alts (d - l)) 
                     (map (pcAlt loc d l) (filter notDef alts)) 
                     (getDefault loc d alts) : []
        pc loc d (BReserve s bc) = RESERVE s : pc loc (d + s) bc ++ 
                                   [CLEAR s]

        notDef (BDefaultCase _) = False
        notDef _ = True

        pcAlt loc d var (BConCase t args l bc)
            = (t, PROJECT (d - var) (d - l) (length args) :
                  pc loc d bc)
        pcAlt loc d var (BConstCase (I c) bc)
            = (c, pc loc d bc)

        getDefault loc d (BDefaultCase bc : _) = pc loc d bc
        getDefault loc d (_ : xs) = getDefault loc d xs
        getDefault loc d [] = []

        caseTy (BConCase _ _ _ _ : _) = CTag
        caseTy (BConstCase _ _ : _) = CIntVal
        caseTy (_ : xs) = caseTy xs
        caseTy [] = CTag



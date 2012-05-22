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
          | CTailApp CAtom [CAtom]
          | CLazy CAtom [CAtom]
          | CFCall String CType [(CAtom, CType)]
          | CPrimOp SPrim [CAtom]
          | CCon Tag [CAtom] 
    deriving Show

data CVal = CTag Local | CIntVal Local
    deriving Show

-- Assignment is to the return value, or some local register
data Reg = RVal | LVar Local
    deriving Show

data CInst = ASSIGN Reg CExp
           | RESERVE Int
           | EVAL Local
           | PROJECT Local Local Int
           | SWITCH CVal [(Int, PreC)] PreC
           | ERROR String
           | TAILCALL CAtom [CAtom]
    deriving Show

type PreC = [CInst]

preCdefs :: [(Name, Bytecode)] -> [(Name, (Int, PreC))]
preCdefs = map (\ (n, b) -> (n, preC b))

atom (BP n) = CP n
atom (BL n) = CL n
atom (BC c) = CC c

preC :: Bytecode -> (Int, PreC)
preC (BGetArgs ns bc) = (length ns, pc RVal bc) 
  where pc loc (BAtom b) = [ASSIGN loc (CAtom (atom b))]
        pc loc (BApp f as) = [ASSIGN loc (CApp (atom f) (map atom as))]
        pc loc (BTailApp f as) = [TAILCALL (atom f) (map atom as)]
        pc loc (BLazy f as) = [ASSIGN loc (CLazy (atom f) (map atom as))]
        pc loc (BLet x val sc) = pc (LVar x) val ++ pc loc sc 
        pc loc (BFCall c t args) 
            = [ASSIGN loc (CFCall c t (map (\ (a, ty) -> (atom a, ty)) args))]
        pc loc (BCon t args) = [ASSIGN loc (CCon t (map atom args))]
        pc loc (BPrimOp s args)
            = [ASSIGN loc (CPrimOp s (map atom args))]
        pc loc (BError s) = [ERROR s]
        pc loc (BCase l alts)
            = EVAL l :
              SWITCH (caseTy alts l) (map (pcAlt loc l) (filter notDef alts)) 
                                     (getDefault loc alts) : []
        pc loc (BReserve s bc) = RESERVE s : pc loc bc

        notDef (BDefaultCase _) = False
        notDef _ = True

        pcAlt loc var (BConCase t args l bc)
            = (t, PROJECT var l (length args) :
                  pc loc bc)
        pcAlt loc var (BConstCase (I c) bc)
            = (c, pc loc bc)

        getDefault loc (BDefaultCase bc : _) = pc loc bc
        getDefault loc (_ : xs) = getDefault loc xs
        getDefault loc [] = []

        caseTy (BConCase _ _ _ _ : _) = CTag
        caseTy (BConstCase _ _ : _) = CIntVal
        caseTy (_ : xs) = caseTy xs
        caseTy [] = CTag



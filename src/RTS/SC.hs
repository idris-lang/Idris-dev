module RTS.SC where

import Core.TT
import Core.Evaluate
import Core.CaseTree

import Control.Monad.State

type CType = Maybe Const
type Tag = Int
type Arity = Int

data SCDef = SCDef { sc_args :: [(Name, CType)],
                     sc_def :: SCExp }
    deriving Show

data SCExp = SVar Name
           | SApp Name [SCExp]
           | SFCall String CType [(SCExp, CType)]
           | SCon Tag [SCExp]
           | SConst Const
           | SErased
           | SCase [SAlt]
    deriving Show

data SAlt = SConCase Tag [Name] SCExp
          | SConstCase Const SCExp
          | SDefaultCase SCExp
    deriving Show

sclift :: (Name, Def) -> [(Name, SCDef)]
sclift d = execState (sc d) [] 

add :: a -> State [a] ()
add x = do xs <- get
           put (x : xs)

class Lift s t | s -> t where
    sc :: s -> State [(Name, SCDef)] t

instance Lift (Name, Def) () where
    sc (n, d) = do d' <- sc d
                   add (n, d')

instance Lift Def SCDef where
    sc x = undefined


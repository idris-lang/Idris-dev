{-# LANGUAGE PatternGuards #-}

module Idris.Transforms where

import Idris.AbsSyntax
import Core.CaseTree
import Core.TT

data TTOpt = TermTrans (TT Name -> TT Name) -- term transform
           | CaseTrans (SC -> SC) -- case expression transform

class Transform a where
     transform :: TTOpt -> a -> a

instance Transform (TT Name) where
    transform o@(TermTrans t) tm = trans t tm where
      trans t (Bind n b tm) = t $ Bind n (transform o b) (trans t tm)
      trans t (App f a)     = t $ App (trans t f) (trans t a)
      trans t tm            = t tm
    transform _ tm = tm

instance Transform a => Transform (Binder a) where
    transform t (Let ty v) = Let (transform t ty) (transform t v)
    transform t b = b { binderTy = transform t (binderTy b) }

instance Transform SC where
    transform o@(CaseTrans t) sc = trans t sc where
      trans t (Case n alts) = t (Case n (map (transform o) alts))
      trans t x = t x
    transform o@(TermTrans t) sc = trans t sc where
      trans t (Case n alts) = Case n (map (transform o) alts)
      trans t (STerm tm) = STerm (t tm)
      trans t x = x

instance Transform CaseAlt where
   transform o (ConCase n i ns sc) = ConCase n i ns (transform o sc)
   transform o (ConstCase c sc)    = ConstCase c (transform o sc)
   transform o (DefaultCase sc)    = DefaultCase (transform o sc)

natTrans = [TermTrans zero, TermTrans suc, CaseTrans natcase]

zname = NS (UN "O") ["nat","prelude"] 
sname = NS (UN "S") ["nat","prelude"] 

zero :: TT Name -> TT Name
zero (P _ n _) | n == zname
    = Constant (BI 0)
zero x = x

suc :: TT Name -> TT Name
suc (App (P _ s _) a) | s == sname
    = mkApp (P Ref (UN "prim__addBigInt") Erased) [Constant (BI 1), a]
suc x = x

natcase :: SC -> SC
natcase = undefined 


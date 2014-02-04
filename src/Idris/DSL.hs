{-# LANGUAGE PatternGuards #-}

module Idris.DSL where

import Idris.AbsSyntax
import Paths_idris

import Idris.Core.TT
import Idris.Core.Evaluate

import Control.Monad.State.Strict
import Debug.Trace

debindApp :: SyntaxInfo -> PTerm -> PTerm
debindApp syn t = debind (dsl_bind (dsl_info syn)) t

desugar :: SyntaxInfo -> IState -> PTerm -> PTerm
desugar syn i t = let t' = expandDo (dsl_info syn) t in
                      t' -- addImpl i t'

expandDo :: DSL -> PTerm -> PTerm
expandDo dsl (PLam n ty tm)
    | Just lam <- dsl_lambda dsl
        = let sc = PApp (fileFC "(dsl)") lam [pexp (var dsl n tm 0)] in
              expandDo dsl sc
expandDo dsl (PLam n ty tm) = PLam n (expandDo dsl ty) (expandDo dsl tm)
expandDo dsl (PLet n ty v tm)
    | Just letb <- dsl_let dsl
        = let sc = PApp (fileFC "(dsl)") letb [pexp v, pexp (var dsl n tm 0)] in
              expandDo dsl sc
expandDo dsl (PLet n ty v tm) = PLet n (expandDo dsl ty) (expandDo dsl v) (expandDo dsl tm)
expandDo dsl (PPi p n ty tm) = PPi p n (expandDo dsl ty) (expandDo dsl tm)
expandDo dsl (PApp fc t args) = PApp fc (expandDo dsl t)
                                        (map (fmap (expandDo dsl)) args)
expandDo dsl (PAppBind fc t args) = PAppBind fc (expandDo dsl t)
                                                (map (fmap (expandDo dsl)) args)
expandDo dsl (PCase fc s opts) = PCase fc (expandDo dsl s)
                                        (map (pmap (expandDo dsl)) opts)
expandDo dsl (PEq fc l r) = PEq fc (expandDo dsl l) (expandDo dsl r)
expandDo dsl (PPair fc p l r) = PPair fc p (expandDo dsl l) (expandDo dsl r)
expandDo dsl (PDPair fc l t r) = PDPair fc (expandDo dsl l) (expandDo dsl t)
                                           (expandDo dsl r)
expandDo dsl (PAlternative a as) = PAlternative a (map (expandDo dsl) as)
expandDo dsl (PHidden t) = PHidden (expandDo dsl t)
expandDo dsl (PNoImplicits t) = PNoImplicits (expandDo dsl t)
expandDo dsl (PUnifyLog t) = PUnifyLog (expandDo dsl t)
expandDo dsl (PDisamb ns t) = PDisamb ns (expandDo dsl t)
expandDo dsl (PReturn fc) = dsl_return dsl
expandDo dsl (PRewrite fc r t ty)
    = PRewrite fc r (expandDo dsl t) ty
expandDo dsl (PGoal fc r n sc)
    = PGoal fc (expandDo dsl r) n (expandDo dsl sc)
expandDo dsl (PDoBlock ds)
    = expandDo dsl $ debind (dsl_bind dsl) (block (dsl_bind dsl) ds)
  where
    block b [DoExp fc tm] = tm
    block b [a] = PElabError (Msg "Last statement in do block must be an expression")
    block b (DoBind fc n tm : rest)
        = PApp fc b [pexp tm, pexp (PLam n Placeholder (block b rest))]
    block b (DoBindP fc p tm : rest)
        = PApp fc b [pexp tm, pexp (PLam (sMN 0 "bpat") Placeholder
                                   (PCase fc (PRef fc (sMN 0 "bpat"))
                                             [(p, block b rest)]))]
    block b (DoLet fc n ty tm : rest)
        = PLet n ty tm (block b rest)
    block b (DoLetP fc p tm : rest)
        = PCase fc tm [(p, block b rest)]
    block b (DoExp fc tm : rest)
        = PApp fc b
            [pexp tm,
             pexp (PLam (sMN 0 "bindx") Placeholder (block b rest))]
    block b _ = PElabError (Msg "Invalid statement in do block")

expandDo dsl (PIdiom fc e) = expandDo dsl $ unIdiom (dsl_apply dsl) (dsl_pure dsl) fc e
expandDo dsl t = t

var :: DSL -> Name -> PTerm -> Int -> PTerm
var dsl n t i = v' i t where
    v' i (PRef fc x) | x == n =
        case dsl_var dsl of
            Nothing -> PElabError (Msg "No 'variable' defined in dsl")
            Just v -> PApp fc v [pexp (mkVar fc i)]
    v' i (PLam n ty sc)
        | Nothing <- dsl_lambda dsl
            = PLam n ty (v' i sc)
        | otherwise = PLam n (v' i ty) (v' (i + 1) sc)
    v' i (PLet n ty val sc)
        | Nothing <- dsl_let dsl
            = PLet n (v' i ty) (v' i val) (v' i sc)
        | otherwise = PLet n (v' i ty) (v' i val) (v' (i + 1) sc)
    v' i (PPi p n ty sc) = PPi p n (v' i ty) (v' i sc)
    v' i (PTyped l r)    = PTyped (v' i l) (v' i r)
    v' i (PApp f x as)   = PApp f (v' i x) (fmap (fmap (v' i)) as)
    v' i (PCase f t as)  = PCase f (v' i t) (fmap (pmap (v' i)) as)
    v' i (PEq f l r)     = PEq f (v' i l) (v' i r)
    v' i (PPair f p l r) = PPair f p (v' i l) (v' i r)
    v' i (PDPair f l t r) = PDPair f (v' i l) (v' i t) (v' i r)
    v' i (PAlternative a as) = PAlternative a $ map (v' i) as
    v' i (PHidden t)     = PHidden (v' i t)
    v' i (PIdiom f t)    = PIdiom f (v' i t)
    v' i (PDoBlock ds)   = PDoBlock (map (fmap (v' i)) ds)
    v' i (PNoImplicits t) = PNoImplicits (v' i t)
    v' i t = t

    mkVar fc 0 = case index_first dsl of
                   Nothing -> PElabError (Msg "No index_first defined")
                   Just f  -> f
    mkVar fc n = case index_next dsl of
                   Nothing -> PElabError (Msg "No index_next defined")
                   Just f -> PApp fc f [pexp (mkVar fc (n-1))]

unIdiom :: PTerm -> PTerm -> FC -> PTerm -> PTerm
unIdiom ap pure fc e@(PApp _ _ _) = let f = getFn e in
                                        mkap (getFn e)
  where
    getFn (PApp fc f args) = (PApp fc pure [pexp f], args)
    getFn f = (f, [])

    mkap (f, [])   = f
    mkap (f, a:as) = mkap (PApp fc ap [pexp f, a], as)

unIdiom ap pure fc e = PApp fc pure [pexp e]

debind :: PTerm -> PTerm -> PTerm
-- For every arg which is an AppBind, lift it out
debind b tm = let (tm', (bs, _)) = runState (db' tm) ([], 0) in
                  bindAll (reverse bs) tm'
  where
    db' :: PTerm -> State ([(Name, FC, PTerm)], Int) PTerm
    db' (PAppBind _ (PApp fc t args) [])
         = db' (PAppBind fc t args)
    db' (PAppBind fc t args)
        = do args' <- dbs args
             (bs, n) <- get
             let nm = sUN ("_bindApp" ++ show n)
             put ((nm, fc, PApp fc t args') : bs, n+1)
             return (PRef fc nm)
    db' (PApp fc t args)
         = do t' <- db' t
              args' <- mapM dbArg args
              return (PApp fc t' args')
    db' (PLam n ty sc) = return (PLam n ty (debind b sc))
    db' (PLet n ty v sc) = do v' <- db' v
                              return (PLet n ty v' (debind b sc))
    db' (PCase fc s opts) = do s' <- db' s
                               return (PCase fc s' (map (pmap (debind b)) opts))
    db' (PPair fc p l r) = do l' <- db' l
                              r' <- db' r
                              return (PPair fc p l' r')
    db' (PDPair fc l t r) = do l' <- db' l
                               r' <- db' r
                               return (PDPair fc l' t r')
    db' t = return t

    dbArg a = do t' <- db' (getTm a)
                 return (a { getTm = t' })

    dbs [] = return []
    dbs (a : as) = do let t = getTm a
                      t' <- db' t
                      as' <- dbs as
                      return (a { getTm = t' } : as')

    bindAll [] tm = tm
    bindAll ((n, fc, t) : bs) tm
       = PApp fc b [pexp t, pexp (PLam n Placeholder (bindAll bs tm))]



{-|
Module      : Idris.DSL
Description : Code to deal with DSL blocks.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE PatternGuards #-}

module Idris.DSL where

import Idris.AbsSyntax
import Idris.Core.Evaluate
import Idris.Core.TT

import Control.Monad.State.Strict
import Data.Generics.Uniplate.Data (transform)
import Debug.Trace

debindApp :: SyntaxInfo -> PTerm -> PTerm
debindApp syn t = debind (dsl_bind (dsl_info syn)) t

dslify :: SyntaxInfo -> IState -> PTerm -> PTerm
dslify syn i = transform dslifyApp
  where
    dslifyApp (PApp fc (PRef _ _ f) [a])
        | [d] <- lookupCtxt f (idris_dsls i)
            = desugar (syn { dsl_info = d }) i (getTm a)
    dslifyApp t = t

desugar :: SyntaxInfo -> IState -> PTerm -> PTerm
desugar syn i t = let t' = expandSugar (dsl_info syn) t
                  in dslify syn i t'

mkTTName :: FC -> Name -> PTerm
mkTTName fc n =
    let mkList fc []     = PRef fc [] (sNS (sUN "Nil") ["List", "Prelude"])
        mkList fc (x:xs) = PApp fc (PRef fc [] (sNS (sUN "::") ["List", "Prelude"]))
                                   [ pexp (stringC x)
                                   , pexp (mkList fc xs)]
        stringC = PConstant fc . Str . str
        intC = PConstant fc . I
        reflm n = sNS (sUN n) ["Reflection", "Language"]
    in case n of
         UN nm     -> PApp fc (PRef fc [] (reflm "UN")) [ pexp (stringC nm)]
         NS nm ns  -> PApp fc (PRef fc [] (reflm "NS")) [ pexp (mkTTName fc nm)
                                                        , pexp (mkList fc ns)]
         MN i nm   -> PApp fc (PRef fc [] (reflm "MN")) [ pexp (intC i)
                                                        , pexp (stringC nm)]
         _ -> error "Invalid name from user syntax for DSL name"

expandSugar :: DSL -> PTerm -> PTerm
expandSugar dsl (PLam fc n nfc ty tm)
    | Just lam <- dsl_lambda dsl
        = PApp fc lam [ pexp (mkTTName fc n)
                      , pexp (expandSugar dsl (var dsl n tm 0))]
expandSugar dsl (PLam fc n nfc ty tm) = PLam fc n nfc (expandSugar dsl ty) (expandSugar dsl tm)
expandSugar dsl (PLet fc n nfc ty v tm)
    | Just letb <- dsl_let dsl
        = PApp (fileFC "(dsl)") letb [ pexp (mkTTName fc n)
                                     , pexp (expandSugar dsl v)
                                     , pexp (expandSugar dsl (var dsl n tm 0))]
expandSugar dsl (PLet fc n nfc ty v tm) = PLet fc n nfc (expandSugar dsl ty) (expandSugar dsl v) (expandSugar dsl tm)
expandSugar dsl (PPi p n fc ty tm)
    | Just pi <- dsl_pi dsl
        = PApp (fileFC "(dsl)") pi [ pexp (mkTTName (fileFC "(dsl)") n)
                                   , pexp (expandSugar dsl ty)
                                   , pexp (expandSugar dsl (var dsl n tm 0))]
expandSugar dsl (PPi p n fc ty tm) = PPi p n fc (expandSugar dsl ty) (expandSugar dsl tm)
expandSugar dsl (PApp fc t args) = PApp fc (expandSugar dsl t)
                                        (map (fmap (expandSugar dsl)) args)
expandSugar dsl (PWithApp fc t arg) = PWithApp fc (expandSugar dsl t)
                                                  (expandSugar dsl arg)
expandSugar dsl (PAppBind fc t args) = PAppBind fc (expandSugar dsl t)
                                                (map (fmap (expandSugar dsl)) args)
expandSugar dsl (PCase fc s opts) = PCase fc (expandSugar dsl s)
                                        (map (pmap (expandSugar dsl)) opts)
expandSugar dsl (PIfThenElse fc c t f) =
  PApp fc (PRef NoFC [] (sUN "ifThenElse"))
       [ PExp 0 [] (sMN 0 "condition") $ expandSugar dsl c
       , PExp 0 [] (sMN 0 "whenTrue") $ expandSugar dsl t
       , PExp 0 [] (sMN 0 "whenFalse") $ expandSugar dsl f
       ]
expandSugar dsl (PPair fc hls p l r) = PPair fc hls p (expandSugar dsl l) (expandSugar dsl r)
expandSugar dsl (PDPair fc hls p l t r) = PDPair fc hls p (expandSugar dsl l) (expandSugar dsl t)
                                                          (expandSugar dsl r)
expandSugar dsl (PAlternative ms a as) = PAlternative ms a (map (expandSugar dsl) as)
expandSugar dsl (PHidden t) = PHidden (expandSugar dsl t)
expandSugar dsl (PNoImplicits t) = PNoImplicits (expandSugar dsl t)
expandSugar dsl (PUnifyLog t) = PUnifyLog (expandSugar dsl t)
expandSugar dsl (PDisamb ns t) = PDisamb ns (expandSugar dsl t)
expandSugar dsl (PRewrite fc by r t ty)
    = PRewrite fc by r (expandSugar dsl t) ty
expandSugar dsl (PGoal fc r n sc)
    = PGoal fc (expandSugar dsl r) n (expandSugar dsl sc)
expandSugar dsl (PDoBlock ds)
    = expandSugar dsl $ debind (dsl_bind dsl) (block (dsl_bind dsl) ds)
  where
    block b [DoExp fc tm] = tm
    block b [a] = PElabError (Msg "Last statement in do block must be an expression")
    block b (DoBind fc n nfc tm : rest)
        = PApp fc b [pexp tm, pexp (PLam fc n nfc Placeholder (block b rest))]
    block b (DoBindP fc p tm alts : rest)
        = PApp fc b [pexp tm, pexp (PLam fc (sMN 0 "__bpat") NoFC Placeholder
                                   (PCase fc (PRef fc [] (sMN 0 "__bpat"))
                                             ((p, block b rest) : alts)))]
    block b (DoLet fc n nfc ty tm : rest)
        = PLet fc n nfc ty tm (block b rest)
    block b (DoLetP fc p tm : rest)
        = PCase fc tm [(p, block b rest)]
    block b (DoExp fc tm : rest)
        = PApp fc b
            [pexp tm,
             pexp (PLam fc (sMN 0 "__bindx") NoFC (mkTy tm) (block b rest))]
        where mkTy (PCase _ _ _) = PRef fc [] unitTy
              mkTy (PMetavar _ _) = PRef fc [] unitTy
              mkTy _ = Placeholder
    block b _ = PElabError (Msg "Invalid statement in do block")

expandSugar dsl (PIdiom fc e) = expandSugar dsl $ unIdiom (dsl_apply dsl) (dsl_pure dsl) fc e
expandSugar dsl (PRunElab fc tm ns) = PRunElab fc (expandSugar dsl tm) ns
expandSugar dsl (PConstSugar fc tm) = PConstSugar fc (expandSugar dsl tm)
expandSugar dsl t = t

-- | Replace DSL-bound variable in a term
var :: DSL -> Name -> PTerm -> Int -> PTerm
var dsl n t i = v' i t where
    v' i (PRef fc hl x) | x == n =
        case dsl_var dsl of
            Nothing -> PElabError (Msg "No 'variable' defined in dsl")
            Just v -> PApp fc v [pexp (mkVar fc i)]
    v' i (PLam fc n nfc ty sc)
        | Nothing <- dsl_lambda dsl
            = PLam fc n nfc ty (v' i sc)
        | otherwise = PLam fc n nfc (v' i ty) (v' (i + 1) sc)
    v' i (PLet fc n nfc ty val sc)
        | Nothing <- dsl_let dsl
            = PLet fc n nfc (v' i ty) (v' i val) (v' i sc)
        | otherwise = PLet fc n nfc (v' i ty) (v' i val) (v' (i + 1) sc)
    v' i (PPi p n fc ty sc)
        | Nothing <- dsl_pi dsl
            = PPi p n fc (v' i ty) (v' i sc)
        | otherwise = PPi p n fc (v' i ty) (v' (i+1) sc)
    v' i (PTyped l r)    = PTyped (v' i l) (v' i r)
    v' i (PApp f x as)   = PApp f (v' i x) (fmap (fmap (v' i)) as)
    v' i (PWithApp f x a) = PWithApp f (v' i x) (v' i a)
    v' i (PCase f t as)  = PCase f (v' i t) (fmap (pmap (v' i)) as)
    v' i (PPair f hls p l r) = PPair f hls p (v' i l) (v' i r)
    v' i (PDPair f hls p l t r) = PDPair f hls p (v' i l) (v' i t) (v' i r)
    v' i (PAlternative ms a as) = PAlternative ms a $ map (v' i) as
    v' i (PHidden t)     = PHidden (v' i t)
    v' i (PIdiom f t)    = PIdiom f (v' i t)
    v' i (PDoBlock ds)   = PDoBlock (map (fmap (v' i)) ds)
    v' i (PNoImplicits t) = PNoImplicits (v' i t)
    v' i t = t

    mkVar fc 0 = case index_first dsl of
                   Nothing -> PElabError (Msg "No index_first defined")
                   Just f  -> setFC fc f
    mkVar fc n = case index_next dsl of
                   Nothing -> PElabError (Msg "No index_next defined")
                   Just f -> PApp fc f [pexp (mkVar fc (n-1))]

    setFC fc (PRef _ _ n) = PRef fc [] n
    setFC fc (PApp _ f xs) = PApp fc (setFC fc f) (map (fmap (setFC fc)) xs)
    setFC fc t = t

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
             return (PRef fc [] nm)
    db' (PApp fc t args)
         = do t' <- db' t
              args' <- mapM dbArg args
              return (PApp fc t' args')
    db' (PWithApp fc t arg)
         = do t' <- db' t
              arg' <- db' arg
              return (PWithApp fc t' arg')
    db' (PLam fc n nfc ty sc) = return (PLam fc n nfc ty (debind b sc))
    db' (PLet fc n nfc ty v sc) = do v' <- db' v
                                     return (PLet fc n nfc ty v' (debind b sc))
    db' (PCase fc s opts) = do s' <- db' s
                               return (PCase fc s' (map (pmap (debind b)) opts))
    db' (PPair fc hls p l r) = do l' <- db' l
                                  r' <- db' r
                                  return (PPair fc hls p l' r')
    db' (PDPair fc hls p l t r) = do l' <- db' l
                                     r' <- db' r
                                     return (PDPair fc hls p l' t r')
    db' (PRunElab fc t ns) = fmap (\tm -> PRunElab fc tm ns) (db' t)
    db' (PConstSugar fc tm) = liftM (PConstSugar fc) (db' tm)
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
       = PApp fc b [pexp t, pexp (PLam fc n NoFC Placeholder (bindAll bs tm))]

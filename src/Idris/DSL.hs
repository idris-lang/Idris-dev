{-# LANGUAGE PatternGuards #-}

module Idris.DSL where

import Idris.AbsSyntax
import Paths_idris

import Core.CoreParser
import Core.TT
import Core.Evaluate

import Debug.Trace

desugar :: SyntaxInfo -> IState -> PTerm -> PTerm
desugar syn i t = let t' = expandDo (dsl_info syn) t in
                      t' -- addImpl i t'

expandDo :: DSL -> PTerm -> PTerm
expandDo dsl (PLam n ty tm)
    | Just lam <- dsl_lambda dsl 
        = let sc = PApp (FC "(dsl)" 0) lam [pexp (var dsl n tm 0)] in
              expandDo dsl sc
expandDo dsl (PLam n ty tm) = PLam n (expandDo dsl ty) (expandDo dsl tm)
expandDo dsl (PLet n ty v tm)
    | Just letb <- dsl_let dsl
        = let sc = PApp (FC "(dsl)" 0) letb [pexp v, pexp (var dsl n tm 0)] in
              expandDo dsl sc
expandDo dsl (PLet n ty v tm) = PLet n (expandDo dsl ty) (expandDo dsl v) (expandDo dsl tm)
expandDo dsl (PPi p n ty tm) = PPi p n (expandDo dsl ty) (expandDo dsl tm)
expandDo dsl (PApp fc t args) = PApp fc (expandDo dsl t)
                                        (map (fmap (expandDo dsl)) args)
expandDo dsl (PCase fc s opts) = PCase fc (expandDo dsl s)
                                        (map (pmap (expandDo dsl)) opts)
expandDo dsl (PPair fc l r) = PPair fc (expandDo dsl l) (expandDo dsl r)
expandDo dsl (PDPair fc l t r) = PDPair fc (expandDo dsl l) (expandDo dsl t) 
                                           (expandDo dsl r)
expandDo dsl (PAlternative as) = PAlternative (map (expandDo dsl) as)
expandDo dsl (PHidden t) = PHidden (expandDo dsl t)
expandDo dsl (PReturn fc) = dsl_return dsl
expandDo dsl (PDoBlock ds) = expandDo dsl $ block (dsl_bind dsl) ds 
  where
    block b [DoExp fc tm] = tm 
    block b [a] = PElabError (Msg "Last statement in do block must be an expression")
    block b (DoBind fc n tm : rest)
        = PApp fc b [pexp tm, pexp (PLam n Placeholder (block b rest))]
    block b (DoBindP fc p tm : rest)
        = PApp fc b [pexp tm, pexp (PLam (MN 0 "bpat") Placeholder 
                                   (PCase fc (PRef fc (MN 0 "bpat"))
                                             [(p, block b rest)]))]
    block b (DoLet fc n ty tm : rest)
        = PLet n ty tm (block b rest)
    block b (DoLetP fc p tm : rest)
        = PCase fc tm [(p, block b rest)]
    block b (DoExp fc tm : rest)
        = PApp fc b 
            [pexp tm, 
             pexp (PLam (MN 0 "bindx") Placeholder (block b rest))]
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
    v' i (PPair f l r)   = PPair f (v' i l) (v' i r)
    v' i (PDPair f l t r) = PDPair f (v' i l) (v' i t) (v' i r)
    v' i (PAlternative as) = PAlternative $ map (v' i) as
    v' i (PHidden t)     = PHidden (v' i t)
    v' i (PIdiom f t)    = PIdiom f (v' i t)
    v' i (PDoBlock ds)   = PDoBlock (map (fmap (v' i)) ds)
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


module Test.Random

import Effects
import Effect.Random

genKVPair : (genA : Eff a [RND])
         -> (genB : Eff b [RND])
         -> Eff (Pair a b) [RND]
genKVPair f g = pure (!f, !g)

genRndListKVUE : (Eq a, Eq b) =>
                 (seed : Integer)
              -> (len  : Nat)
              -> (genA : Eff a [RND])
              -> (genB : Eff b [RND])
              -> Eff (List (Pair a b)) [RND]
genRndListKVUE s l f g = do srand s; pure !(doGen l (genKVPair f g))
  where
    genElem : (Eq a, Eq b)
           => (generator : Eff (Pair a b) [RND])
           -> (existing  : List (Pair a b))
           -> Eff (Pair a b) [RND]
    genElem j xs = do
      x <- j
      if elem x xs
        then genElem j xs
        else if isJust $ lookup (fst x) xs
          then genElem j xs
          else pure x

    doGen : (Eq a, Eq b)
         => (count     : Nat)
         -> (generator : Eff (Pair a b) [RND])
         -> Eff (List (Pair a b)) [RND]
    doGen Z     j = pure Nil
    doGen (S n) j = do
      xs <- doGen n j
      x  <- genElem j xs
      pure (x::xs)

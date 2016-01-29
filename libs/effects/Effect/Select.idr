module Effect.Select

import Effects

%access public export

data Selection : Effect where
     Select : List a -> sig Selection a ()

implementation Handler Selection Maybe where
     handle _ (Select xs) k = tryAll xs where
         tryAll [] = Nothing
         tryAll (x :: xs) = case k x () of
                                 Nothing => tryAll xs
                                 Just v => Just v

implementation Handler Selection List where
     handle r (Select xs) k = concatMap (\x => k x r) xs

SELECT : EFFECT
SELECT = MkEff () Selection

select : List a -> Eff a [SELECT]
select xs = call $ Select xs


module Effect.Select

import Effects

data Selection : Effect where
     Select : List a -> { () } Selection a 

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

select : List a -> { [SELECT] } Eff m a 
select xs = call $ Select xs


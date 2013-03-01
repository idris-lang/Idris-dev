module Effect.Select

import Effects

data Selection : Effect where
     Select : List a -> Selection () () a

instance Handler Selection Maybe where
     handle _ (Select xs) k = tryAll xs where
         tryAll [] = Nothing
         tryAll (x :: xs) = case k () x of
                                 Nothing => tryAll xs
                                 Just v => Just v

instance Handler Selection List where
     handle r (Select xs) k = concatMap (k r) xs
     
SELECT : EFF
SELECT = MkEff () Selection

select : List a -> Eff m [SELECT] a
select xs = Select xs


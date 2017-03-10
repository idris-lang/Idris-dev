%default total

data Level : Type where
  SL : Inf Level -> Level

sLevelNotSLevel' : (level : Inf Level) ->
                   Not (SL level = SL level)
sLevelNotSLevel' (SL (Delay level)) p = sLevelNotSLevel' level Refl

sLevelNotSLevel : (level : Level) ->
                  Not (SL (Delay level) = SL (Delay level))
sLevelNotSLevel (SL (Delay level)) p = sLevelNotSLevel' level Refl

l : Level
l = SL l

v : Void
v = sLevelNotSLevel l Refl

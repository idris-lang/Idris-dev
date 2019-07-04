module Data.Bool.Extra

%access public export
%default total

notInvolutive : (x : Bool) -> not (not x) = x
notInvolutive True  = Refl
notInvolutive False = Refl

-- AND

andSameNeutral : (x : Bool) -> x && x = x
andSameNeutral False = Refl
andSameNeutral True = Refl

andFalseFalse : (x : Bool) -> x && False = False
andFalseFalse False = Refl
andFalseFalse True = Refl

andTrueNeutral : (x : Bool) -> x && True = x
andTrueNeutral False = Refl
andTrueNeutral True = Refl

andAssociative : (x, y, z : Bool) -> x && (y && z) = (x && y) && z
andAssociative True  _ _ = Refl
andAssociative False _ _ = Refl

andCommutative : (x, y : Bool) -> x && y = y && x
andCommutative x True  = andTrueNeutral x
andCommutative x False = andFalseFalse x

andNotFalse : (x : Bool) -> x && not x = False
andNotFalse False = Refl
andNotFalse True = Refl

-- OR

orSameNeutral : (x : Bool) -> x || x = x
orSameNeutral False = Refl
orSameNeutral True = Refl

orFalseNeutral : (x : Bool) -> x || False = x
orFalseNeutral False = Refl
orFalseNeutral True = Refl

orTrueTrue : (x : Bool) -> x || True = True
orTrueTrue False = Refl
orTrueTrue True = Refl

orAssociative : (x, y, z : Bool) -> x || (y || z) = (x || y) || z
orAssociative True  _ _ = Refl
orAssociative False _ _ = Refl

orCommutative : (x, y : Bool) -> x || y = y || x
orCommutative x True  = orTrueTrue x
orCommutative x False = orFalseNeutral x

orNotTrue : (x : Bool) -> x || not x = True
orNotTrue False = Refl
orNotTrue True = Refl

-- interaction & De Morgan's laws

orSameAndRightNeutral : (x, y : Bool) -> x || (x && y) = x
orSameAndRightNeutral False _ = Refl
orSameAndRightNeutral True  _ = Refl

andDistribOrR : (x, y, z : Bool) -> x && (y || z) = (x && y) || (x && z)
andDistribOrR False _ _ = Refl
andDistribOrR True  _ _ = Refl

orDistribAndR : (x, y, z : Bool) -> x || (y && z) = (x || y) && (x || z)
orDistribAndR False _ _ = Refl
orDistribAndR True  _ _ = Refl

notAndIsOr : (x, y : Bool) -> not (x && y) = not x || not y
notAndIsOr False _ = Refl
notAndIsOr True  _ = Refl

notOrIsAnd : (x, y : Bool) -> not (x || y) = not x && not y
notOrIsAnd False _ = Refl
notOrIsAnd True  _ = Refl

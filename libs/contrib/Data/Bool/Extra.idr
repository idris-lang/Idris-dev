module Data.Bool.Extra

%access public export
%default total

andSameNeutral : (x : Bool) -> x && x = x
andSameNeutral False = Refl
andSameNeutral True = Refl

andFalseFalse : (x : Bool) -> x && False = False
andFalseFalse False = Refl
andFalseFalse True = Refl

andTrueNeutral : (x : Bool) -> x && True = x
andTrueNeutral False = Refl
andTrueNeutral True = Refl

orSameNeutral : (x : Bool) -> x || x = x
orSameNeutral False = Refl
orSameNeutral True = Refl

orFalseNeutral : (x : Bool) -> x || False = x
orFalseNeutral False = Refl
orFalseNeutral True = Refl

orTrueTrue : (x : Bool) -> x || True = True
orTrueTrue False = Refl
orTrueTrue True = Refl

orSameAndRightNeutral : (x, right : Bool) -> x || (x && right) = x
orSameAndRightNeutral False _ = Refl
orSameAndRightNeutral True _ = Refl

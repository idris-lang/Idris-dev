module Control.Functor.Constant

import Prelude.Algebra
import Prelude.Functor
import Prelude.Applicative

public record Constant : Set -> Set -> Set where
    Const : (runConstant : a) -> Constant a b

--instance Functor (Constant a) where
--    fmap _ (Const a) = Const a

--instance Monoid a => Applicative (Constant a) where
--    pure _ = Const neutral
--    
--    (Const a) <$> (Const b) = Const (a <+> b)

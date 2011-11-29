module prelude.either;

import builtins;

data Either a b = Left a | Right b;

choose : (b : Bool) -> Either (so b) (so (not b));
choose True = Left oh;
choose False = Right oh;


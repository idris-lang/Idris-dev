import Data.So

antitrue : So False -> a
antitrue Oh impossible

total
prf : (a:Nat) -> (b:Nat) -> So (a > b) -> GT a b
prf Z     Z     Oh impossible
prf Z     (S k) um = antitrue um
prf (S k) Z     um = LTESucc LTEZero 
-- prf (S x) (S y) Oh impossible



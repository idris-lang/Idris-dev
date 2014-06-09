antitrue : so False -> a
antitrue oh impossible

total
prf : (a:Nat) -> (b:Nat) -> so (a > b) -> GT a b
prf Z     Z     oh impossible
prf Z     (S k) um = antitrue um
prf (S k) Z     um = lteSucc lteZero 
-- prf (S _) (S _) oh impossible



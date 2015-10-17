module DefaultArgSubstitutionSyntax

DecProofType : {a:Type} -> Dec a -> Type
DecProofType {a} (Yes _)  = a
DecProofType {a} (No _)   = a -> Void

decProof : {a:Type} -> (dec : Dec a) -> DecProofType dec
decProof (Yes x)  = x
decProof (No x)   = x

DecType : {a:Type} -> Dec a -> Type
DecType {a} _ = a


syntax "{{" [prfname] ":" "accept" [dec] "}}" "->" [ret] 
  = { default (decProof dec) prfname : DecType dec } -> ret

syntax "{{" [prfname] ":" "reject" [dec] "}}" "->" [ret] 
  = { default (decProof dec) prfname : DecType dec -> Void } -> ret


argsAreSame : (n:Nat) -> (m:Nat)
              -> {{ same : accept (decEq n m) }} -> ()
argsAreSame _ _ = ()


argsAreDiff : (n:Nat) -> (m:Nat)
              -> {{ diff : reject (decEq m n) }} -> ()
argsAreDiff _ _ = ()


data SameNats : Type where
  Same : (n:Nat) -> (m:Nat) -> {{ same : accept (decEq m n) }} -> SameNats

data DiffNats : Type where
  Diff : (n:Nat) -> (m:Nat) -> {{ diff : reject (decEq m n) }} -> DiffNats


zArgsAreSame : ()
zArgsAreSame = argsAreSame Z Z

zszArgsAreDiff : ()
zszArgsAreDiff = argsAreDiff Z (S Z)

sameNatZs : SameNats
sameNatZs = Same Z Z

diffNatsZSZ : DiffNats
diffNatsZSZ = Diff Z (S Z)

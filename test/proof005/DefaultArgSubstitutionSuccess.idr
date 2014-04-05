module DefaultArgSubstitutionSuccess

DecProofType : {a:Type} -> Dec a -> Type
DecProofType {a} (Yes _)  = a
DecProofType {a} (No _)   = a -> _|_

decProof : {a:Type} -> (dec : Dec a) -> DecProofType dec
decProof (Yes x)  = x
decProof (No x)   = x

DecType : {a:Type} -> Dec a -> Type
DecType {a} _ = a


argsAreSame : (n:Nat) -> (m:Nat)
              -> { default (decProof (decEq m n)) same : (m=n) } -> ()
argsAreSame _ _ = ()

data SameNats : Type where
  same : (n:Nat) -> (m:Nat) ->
         { default (decProof (decEq m n)) same : (m=n) } -> SameNats

zArgsAreSame : ()
zArgsAreSame = argsAreSame Z Z

sameNatZs : SameNats
sameNatZs = same Z Z

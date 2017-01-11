module Test

import Data.Vect
%default total 

genT : Vect n Type -> Type
genT [] = Type
genT (x :: xs) = x -> genT xs

data FunLang: Type where
  Atom : {dt : Vect n Type} -> genT dt -> FunLang 
  And  : FunLang -> FunLang -> FunLang
  Uor  : FunLang -> FunLang -> FunLang
  Xor  : FunLang -> FunLang -> FunLang  -- d decides on that

data IndexFL : FunLang -> FunLang -> Type where
  LHere     : IndexFL fl fl
  LLeftAnd  : IndexFL x rfl -> IndexFL (And x y) rfl
  LRightAnd : IndexFL y rfl -> IndexFL (And x y) rfl
  LLeftUor  : IndexFL x rfl -> IndexFL (Uor x y) rfl
  LRightUor : IndexFL y rfl -> IndexFL (Uor x y) rfl
  LLeftXor  : IndexFL x rfl -> IndexFL (Xor x y) rfl
  LRightXor : IndexFL y rfl -> IndexFL (Xor x y) rfl

data SetFL : FunLang -> Type where
  SEmpty      : SetFL fl
  SElem      : SetFL fl
  SLeftAnd   : SetFL x -> SetFL (And x y) 
  SRightAnd  : SetFL y -> SetFL (And x y) 
  SBothAnd   : SetFL x -> SetFL y -> SetFL (And x y) 
  SLeftUor   : SetFL x -> SetFL (Uor x y) 
  SRightUor : SetFL y -> SetFL (Uor x y) 
  SBothUor   : SetFL x -> SetFL y -> SetFL (Uor x y) 
  SLeftXor   : SetFL x -> SetFL (Xor x y) 
  SRightXor  : SetFL y -> SetFL (Xor x y) 
  SBothXor   : SetFL x -> SetFL y -> SetFL (Xor x y) 

addIndexFLEmpty : IndexFL fl _ -> SetFL fl
addIndexFLEmpty LHere = SElem
addIndexFLEmpty (LLeftAnd z) = SLeftAnd $ addIndexFLEmpty z
addIndexFLEmpty (LRightAnd z) = SRightAnd $ addIndexFLEmpty z
addIndexFLEmpty (LLeftUor z) = SLeftUor $ addIndexFLEmpty z
addIndexFLEmpty (LRightUor z) = SRightUor $ addIndexFLEmpty z
addIndexFLEmpty (LLeftXor z) = SLeftXor $ addIndexFLEmpty z
addIndexFLEmpty (LRightXor z) =  SRightXor $ addIndexFLEmpty z

addIndexFL : SetFL fl -> IndexFL fl _ -> SetFL fl
addIndexFL SEmpty y = addIndexFLEmpty y
addIndexFL SElem y = SElem
addIndexFL x LHere = SElem
addIndexFL (SLeftAnd x) (LLeftAnd w) = SLeftAnd $ addIndexFL x w
addIndexFL (SLeftAnd SElem) (LRightAnd LHere) = SElem
addIndexFL (SLeftAnd x) (LRightAnd w) = SBothAnd x (addIndexFLEmpty w)
addIndexFL (SRightAnd SElem) (LLeftAnd LHere) = SElem
addIndexFL (SRightAnd x) (LLeftAnd w) = SBothAnd (addIndexFLEmpty w) x
addIndexFL (SRightAnd x) (LRightAnd w) = SRightAnd $ addIndexFL x w
addIndexFL (SBothAnd x SElem) (LLeftAnd LHere) = SElem
addIndexFL (SBothAnd SElem y) (LRightAnd LHere) = SElem
addIndexFL (SBothAnd x y) (LLeftAnd w) = SBothAnd (addIndexFL x w) y
addIndexFL (SBothAnd x y) (LRightAnd w) = SBothAnd x (addIndexFL y w)
addIndexFL (SLeftUor x) (LLeftUor w) = SLeftUor $ addIndexFL x w
addIndexFL (SLeftUor SElem) (LRightUor LHere) = SElem
addIndexFL (SLeftUor x) (LRightUor w) = SBothUor x (addIndexFLEmpty w)
addIndexFL (SRightUor SElem) (LLeftUor LHere) = SElem
addIndexFL (SRightUor x) (LLeftUor w) = SBothUor (addIndexFLEmpty w) x
addIndexFL (SRightUor x) (LRightUor w) = SRightUor $ addIndexFL x w
addIndexFL (SBothUor x SElem) (LLeftUor LHere) = SElem
addIndexFL (SBothUor SElem y) (LRightUor LHere) = SElem
addIndexFL (SBothUor x y) (LLeftUor w) = SBothUor (addIndexFL x w) y
addIndexFL (SBothUor x y) (LRightUor w) = SBothUor x (addIndexFL y w)
addIndexFL (SLeftXor x) (LLeftXor w) = SLeftXor $ addIndexFL x w
addIndexFL (SLeftXor SElem) (LRightXor LHere) = SElem
addIndexFL (SLeftXor x) (LRightXor w) = SBothXor x (addIndexFLEmpty w)
addIndexFL (SRightXor SElem) (LLeftXor LHere) = SElem
addIndexFL (SRightXor x) (LLeftXor w) = SBothXor (addIndexFLEmpty w) x
addIndexFL (SRightXor x) (LRightXor w) = SRightXor $ addIndexFL x w
addIndexFL (SBothXor x SElem) (LLeftXor LHere) = SElem
addIndexFL (SBothXor SElem y) (LRightXor LHere) = SElem
addIndexFL (SBothXor x y) (LLeftXor w) = SBothXor (addIndexFL x w) y
addIndexFL (SBothXor x y) (LRightXor w) = SBothXor x (addIndexFL y w)


-- Everything here should type check but at some point in the past has
-- not.

import Data.So
import Data.Vect
import Data.HVect
import Data.Fin
import Control.Isomorphism

interface Functor f => VerifiedFunctor (f : Type -> Type) where
   identity : (fa : f a) -> map Basics.id fa = fa

data Imp : Type where
   MkImp : {any : Type} -> any -> Imp

testVal : Imp
testVal = MkImp (apply id Z)

zfin : Fin 1
zfin = 0

data Infer = MkInf a

foo : Infer
foo = MkInf (the (Fin 1) 0)

isAnyBy : (alpha -> Bool) -> (n : Nat ** Vect n alpha) -> Bool
isAnyBy _ (_ ** Nil) = False
isAnyBy p (_ ** (a :: as)) = p a || isAnyBy p (_ ** as)

filterTagP : (p  : alpha -> Bool) ->
             (as : Vect n alpha) ->
             So (isAnyBy p (n ** as)) ->
             (m : Nat ** (Vect m (a : alpha ** So (p a)), So (m > Z)))
filterTagP {n = S m} p (a :: as) q with (p a)
  | True  = (_
             **
             ((a ** believe_me Oh)
              ::
              (fst (snd (filterTagP p as (believe_me Oh)))),
              Oh
             )
            )
  | False = filterTagP p as (believe_me Oh)

vfoldl : (P : Nat -> Type) ->
         ((x : Nat) -> P x -> a -> P (S x)) -> P Z
       -> Vect m a -> P m
vfoldl P cons nil (x :: xs)
    = vfoldl (\k => P (S k)) (\ n => cons (S n)) (cons Z nil x) xs


total soElim            :  (C : (b : Bool) -> So b -> Type) ->
                           C True Oh                       ->
                           (b : Bool) -> (s : So b) -> (C b s)
soElim C coh True Oh  =  coh

soFalseElim             :  So False -> a
soFalseElim x           =  void (soElim C () False x)
                           where
                           C : (b : Bool) -> So b -> Type
                           C True s = ()
                           C False s = Void

soTrue                  :  So b -> b = True
soTrue {b = False} x    =  soFalseElim x
soTrue {b = True}  x    =  Refl

interface Eq alpha => ReflEqEq alpha where
  reflexive_eqeq : (a : alpha) -> So (a == a)

modifyFun : (Eq alpha) =>
            (alpha -> beta) ->
            (alpha, beta) ->
            (alpha -> beta)
modifyFun f (a, b) a' = if a' == a then b else f a'

modifyFunLemma : (ReflEqEq alpha) =>
                 (f : alpha -> beta) ->
                 (ab : (alpha, beta)) ->
                 modifyFun f ab (fst ab) = snd ab
modifyFunLemma f (a,b) =
  rewrite soTrue (reflexive_eqeq a) in Refl


Matrix : Type -> Nat -> Nat -> Type
Matrix a n m = Vect n (Vect m a)

mytranspose : Matrix a (S n) (S m) -> Matrix a (S m) (S n)
mytranspose ((x:: []) :: []) = [[x]]
mytranspose [x :: y :: xs] = [x] :: (mytranspose [y :: xs])
mytranspose (x :: y :: xs)
    = let tx = mytranspose [x] in
      let ux = mytranspose (y :: xs) in zipWith (++) tx ux

using (A : Type, B : A->Type, C : Type)
  foo2 : ((x:A) -> B x -> C) -> ((x:A ** B x) -> C)
  foo2 f p = f (fst p) (snd p)


m_add : Maybe (Either Bool Int) -> Maybe (Either Bool Int) ->
        Maybe (Either Bool Int)
m_add x y = do x' <- x -- Extract value from x
               y' <- y -- Extract value from y
               case x' of
                  Left _ => Nothing
                  Right _ => Nothing

data Ty = TyBool

data Id a = I a

interpTy : Ty -> Type
interpTy TyBool = Id Bool

data Term : Ty -> Type where
  TLit : Bool -> Term TyBool
  TNot : Term TyBool -> Term TyBool

map : (a -> b) -> Id a -> Id b
map f (I x) = I (f x)

interp : Term t -> interpTy t
interp (TLit x) = I x
interp (TNot x) = map not (interp x)

data Result str a = Success str a | Failure String

implementation Functor (Result str) where
   map f (Success s x) = Success s (f x)
   map f (Failure e  ) = Failure e

ParserT : (Type -> Type) -> Type -> Type -> Type
ParserT m str a = str -> m (Result str a)

ap : Monad m => ParserT m str (a -> b) -> ParserT m str a ->
                ParserT m str b
ap f x = \s => do f' <- f s
                  case f' of
                          Failure e => (pure (Failure e))
                          Success s' g => x s' >>= pure . map g

X : Nat -> Type
X t = (c : Nat ** So (c < 5))

column : X t -> Nat
column = fst

data Action = Left | Ahead | Right

admissible : X t -> Action -> Bool
admissible {t} x Ahead = column {t} x == 0 || column {t} x == 4
admissible {t} x Left  = column {t} x <= 2
admissible {t} x Right = column {t} x >= 2


interface Set univ where
  member : univ -> univ -> Type

isSubsetOf : Set univ => univ -> univ -> Type
isSubsetOf {univ} a b = (c : univ) -> (member c a) -> (member c b)

interface Set univ => HasPower univ where
  Powerset : (a : univ) ->
             DPair univ (\Pa => (c : univ) ->
                                 (isSubsetOf c a) -> member c Pa)

powerset : HasPower univ => univ -> univ
powerset {univ} a = fst (Powerset a)

mapFilter : (alpha -> beta) ->
           (alpha -> Bool) ->
           Vect n alpha ->
           (n : Nat ** Vect n beta)
mapFilter f p Nil = (_ ** Nil)
mapFilter f p (a :: as) with (p a)
 | True  = (_  ** (f a) :: (snd (mapFilter f p as)))
 | False = mapFilter f p as

hVectEx1 : HVect [String, List Nat, Nat, (Nat, Nat)]
hVectEx1 = ["Hello",[1,2,3],42,(0,10)]

vecfoo : HVect [String, List Nat, Nat, (Nat, Nat)]
vecfoo = put (S (S Z)) hVectEx1

foom : Monad m => Int -> m Int
foom = pure

bar : IO ()
bar = case foom 5 of
           Nothing => print 42
           Just n => print n

Max : (Nat -> Type) -> Type
Max p = (Nat , (k : Nat) -> p k -> Nat)

maxEquiv : Max p -> (n1 : Nat) -> p n1 -> Nat
maxEquiv a n1 pr1 = snd a n1 pr1

data Rho = R

rho : Rho -> Rho
rho r = case r of R => r

data Kappa : (r : Rho) -> Type where K : Kappa r

kappa : Kappa (rho r) -> Kappa (rho r)
kappa {r} k = k' where -- k' : Kappa (rho r)
                       k' = k

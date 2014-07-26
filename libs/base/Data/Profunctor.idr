module Data.Profunctor

import Data.Morphisms

%access public

||| Formally, the class Profunctor represents a profunctor from Idr -> Idr.
|||
||| Intuitively it is a bifunctor where the first argument is contravariant
||| and the second argument is covariant.
|||
||| You can define a `Profunctor` by either defining `dimap` or by defining both
||| `lmap` and `rmap`.
|||
||| If you supply dimap, you should ensure `dimapId`
|||
||| If you supply lmap and rmap, ensure `lmapId` and `rmapId`
|||
||| If you supply both, you should also ensure `dimapIsLmapRmap`
class Profunctor (p : Type -> Type -> Type) where
	||| Map over both arguments at the same time.
	dimap : (a -> b) -> (c -> d) -> p b c -> p a d
	dimap f g = lmap f . rmap g
	||| Map the first argument contravariantly.
	lmap : (a -> b) -> p b c -> p a c
	lmap f = dimap f id
	||| Map the second argument covariantly.
	rmap : (b -> c) -> p a b -> p a c
	rmap = dimap id

||| These ensure by parametricity:
|||
||| dimap (f . g) (h . i) = dimap g h . dimap f i
||| lmap (f . g) = lmap g . lmap f
||| rmap (f . g) = rmap f . rmap g
class Profunctor p => VerifiedProfunctor (p : Type -> Type -> Type) where
	total dimapId : (f : p a b) -> dimap id id f = id f
	total lmapId : (f : p a b) -> lmap id f = id f
	total rmapId : (f : p a b) -> rmap id f = id f
	total dimapIsLmapRmap : (f : a -> b) -> (g : b -> c) -> dimap f g = lmap f . rmap g

-- TODO: where to put this?
private swap : (a,b) -> (b,a)
swap (a,b) = (b,a)

||| Generalizing `UpStar` of a strong `Functor`
|||
||| Minimal complete definition: `first'` or `second'`
|||
||| Note: Every `Functor` is strong.
|||
||| <http://takeichi.ipl-lab.org/~asada/papers/arrStrMnd.pdf>
class Profunctor p => Strong (p : Type -> Type -> Type) where
	first : p a b  -> p (a, c) (b, c)
	first = dimap swap swap . second
	second : p a b -> p (c, a) (c, b)
	second = dimap swap swap . first

||| The generalization of `DownStar` of a \"costrong\" `Functor`
|||
||| Minimal complete definition: `left'` or `right'`
class Profunctor p => Choice (p : Type -> Type -> Type) where
	left : p a b -> p (Either a c) (Either b c)
	left =  dimap (either Right Left) (either Right Left) . right
	right : p a b -> p (Either c a) (Either c b)
	right =  dimap (either Right Left) (either Right Left) . left

instance Profunctor (\a,b => a -> b) where
	dimap ab cd bc = cd . bc . ab
	lmap = flip (.)
	rmap = (.)

instance Functor m => Profunctor (Kleislimorphism m) where
	dimap f g (Kleisli h) = Kleisli (map g . h . f)
	lmap k (Kleisli f) = Kleisli (f . k)
	rmap k (Kleisli f) = Kleisli (map k . f)



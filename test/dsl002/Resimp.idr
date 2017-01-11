module Resimp

import public Data.Vect
import public Data.Fin

%language DSLNotation
%access public export

-- IO operations which read a resource
data Reader : Type -> Type where
    MkReader : IO a -> Reader a

getReader : Reader a -> IO a
getReader (MkReader x) = x

ior : IO a -> Reader a
ior = MkReader

-- IO operations which update a resource
data Updater : Type -> Type where
    MkUpdater : IO a -> Updater a

getUpdater : Updater a -> IO a
getUpdater (MkUpdater x) = x

iou : IO a -> Updater a
iou = MkUpdater

-- IO operations which create a resource
data Creator : Type -> Type where
    MkCreator : IO a -> Creator a

getCreator : Creator a -> IO a
getCreator (MkCreator x) = x

ioc : IO a -> Creator a
ioc = MkCreator

infixr 5 :->

using (i: Fin n, gam : Vect n Ty, gam' : Vect n Ty, gam'' : Vect n Ty)

  data Ty = R Type
          | Val Type
          | Choice Type Type
          | (:->) Type Ty

  interpTy : Ty -> Type
  interpTy (R t) = IO t
  interpTy (Val t) = t
  interpTy (Choice x y) = Either x y
  interpTy (a :-> b) = a -> interpTy b

  data HasType : Vect n Ty -> Fin n -> Ty -> Type where
       Stop : HasType (a :: gam) FZ a
       Pop  : HasType gam i b -> HasType (a :: gam) (FS i) b

  data Env : Vect n Ty -> Type where
       Nil : Env Nil
       (::) : interpTy a -> Env gam -> Env (a :: gam)

  envLookup : HasType gam i a -> Env gam -> interpTy a
  envLookup Stop    (x :: xs) = x
  envLookup (Pop k) (x :: xs) = envLookup k xs

  update : (gam : Vect n Ty) -> HasType gam i b -> Ty -> Vect n Ty
  update (x :: xs) Stop    y = y :: xs
  update (x :: xs) (Pop k) y = x :: update xs k y
  update Nil       Stop    _ impossible

  total
  envUpdate : (p:HasType gam i a) -> (val:interpTy b) ->
              Env gam -> Env (update gam p b)
  envUpdate Stop    val (x :: xs) = val :: xs
  envUpdate (Pop k) val (x :: xs) = x :: envUpdate k val xs
  envUpdate Stop    _   Nil impossible

  total
  envUpdateVal : (p:HasType gam i a) -> (val:b) ->
              Env gam -> Env (update gam p (Val b))
  envUpdateVal Stop    val (x :: xs) = val :: xs
  envUpdateVal (Pop k) val (x :: xs) = x :: envUpdateVal k val xs
  envUpdateVal Stop    _   Nil impossible

  envTail : Env (a :: gam) -> Env gam
  envTail (x :: xs) = xs

  data Args  : Vect n Ty -> List Type -> Type where
       ANil  : Args gam []
       ACons : HasType gam i a ->
               Args gam as -> Args gam (interpTy a :: as)

  funTy : List Type -> Ty -> Ty
  funTy list.Nil t = t
  funTy (a :: as) t = a :-> funTy as t

  data Res : Vect n Ty -> Vect n Ty -> Ty -> Type where

{-- Resource creation and usage. 'Let' creates a resource - the type
    at the end means that the resource must have been consumed by the time
    it goes out of scope, where "consumed" simply means that it has been
    replaced with a value of type '()'. --}

       Let    : Creator (interpTy a) ->
                Res (a :: gam) (Val () :: gam') (R t) ->
                Res gam gam' (R t)
       Update : (a -> Updater b) -> (p:HasType gam i (Val a)) ->
                Res gam (update gam p (Val b)) (R ())
       Use    : (a -> Reader b) -> HasType gam i (Val a) ->
                Res gam gam (R b)

{-- Control structures --}

       Lift   : IO a -> Res gam gam (R a)
       Check  : (p:HasType gam i (Choice (interpTy a) (interpTy b))) ->
                (failure:Res (update gam p a) (update gam p c) t) ->
                (success:Res (update gam p b) (update gam p c) t) ->
                Res gam (update gam p c) t
       While  : Res gam gam (R Bool) ->
                Res gam gam (R ()) -> Res gam gam (R ())
       Pure : a -> Res gam gam (R a)
       (>>=)  : Res gam gam'  (R a) -> (a -> Res gam' gam'' (R t)) ->
                Res gam gam'' (R t)

  ioret : a -> IO a
  ioret = pure

  interp : Env gam -> %static (e : Res gam gam' t) ->
           (Env gam' -> interpTy t -> IO u) -> IO u

  interp env (Let val scope) k
     = do x <- getCreator val
          interp (x :: env) scope
                   (\env', scope' => k (envTail env') scope')
  interp env (Update method x) k
      = do x' <- getUpdater (method (envLookup x env))
           k (envUpdateVal x x' env) (pure ())
  interp env (Use method x) k
      = do x' <- getReader (method (envLookup x env))
           k env (pure x')
  interp env (Lift io) k
     = k env io
  interp env (Check x left right) k =
     either (\a => interp (envUpdate x a env) left k)
            (\b => interp (envUpdate x b env) right k)
            (envLookup x env)
  interp env (While test body) k
     = interp env test
          (\env', result =>
             do r <- result
                if (not r)
                   then (k env' (pure ()))
                   else (interp env' body
                        (\env'', body' =>
                           do v <- body' -- make sure it's evalled
                              interp env'' (While test body) k )))
  interp env (Pure v) k = k env (pure v)
  interp env (v >>= f) k
     = interp env v (\env', v' => do n <- v'
                                     interp env' (f n) k)

  let_ : _ -> Creator (interpTy a) ->
              Res (a :: gam) (Val () :: gam') (R t) ->
              Res gam gam' (R t)
  let_ _ = Let

--   run : {static} Res [] [] (R t) -> IO t
--   run prog = interp [] prog (\env, res => res)

syntax run [prog] = interp [] prog (\env, res => res)

dsl res
   variable = id
   let = let_
   index_first = Stop
   index_next = Pop

syntax RES [x] = {gam:Vect n Ty} -> Res gam gam (R x)


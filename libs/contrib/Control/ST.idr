module Control.ST

import Language.Reflection.Utils

%default total

infix 5 :::

{- A resource is a pair of a label and the current type stored there -}
public export
data Resource : Type where
     MkRes : label -> Type -> Resource

export
data Var = MkVar -- Phantom, just for labelling purposes

%error_reverse
public export
(:::) : Var -> Type -> Resource
(:::) = MkRes

{- Contexts for holding current resources states -}
namespace Resources
  public export
  data Resources : Type where
       Nil : Resources
       (::) : Resource -> Resources -> Resources

  public export
  (++) : Resources -> Resources -> Resources
  (++) [] ys = ys
  (++) (x :: xs) ys = x :: xs ++ ys

{- Proof that a label has a particular type in a given context -}
public export
data InState : Var -> Type -> Resources -> Type where
     Here : InState lbl st (MkRes lbl st :: rs)
     There : InState lbl st rs -> InState lbl st (r :: rs)

{- Update an entry in a context with a new state -}
public export
updateRes : (res : Resources) ->
             InState lbl st res -> Type -> Resources
updateRes (MkRes lbl _ :: rs) Here val = (MkRes lbl val :: rs)
updateRes (r :: rs) (There x) ty = r :: updateRes rs x ty

{- Remove an entry from a context -}
public export
drop : (res : Resources) -> (prf : InState lbl st res) ->
       Resources
drop (MkRes lbl st :: rs) Here = rs
drop (r :: rs) (There p) = r :: drop rs p

{- Proof that a resource state (label/type) is in a context -}
public export
data ElemRes : Resource -> Resources -> Type where
     HereRes : ElemRes a (a :: as)
     ThereRes : ElemRes a as -> ElemRes a (b :: as)

public export %error_reduce
dropEl : (ys: _) -> ElemRes x ys -> Resources
dropEl (x :: as) HereRes = as
dropEl (x :: as) (ThereRes p) = x :: dropEl as p

{- Proof that a variable name is in a context -}
public export
data VarInRes : Var -> Resources -> Type where
     VarHere   : VarInRes a (MkRes a st :: as)
     VarThere  : VarInRes a as -> VarInRes a (b :: as)

public export %error_reduce
dropVarIn : (ys: _) -> VarInRes x ys -> Resources
dropVarIn ((MkRes x _) :: as) VarHere = as
dropVarIn (x :: as) (VarThere p) = x :: dropVarIn as p

public export
data Composite : List Type -> Type where
     CompNil : Composite []
     CompCons : (x : a) -> Composite as -> Composite (a :: as)

namespace VarList
  public export
  data VarList : List Type -> Type where
       Nil : VarList []
       (::) : Var -> VarList ts -> VarList (t :: ts)

  public export
  mkRes : VarList tys -> Resources
  mkRes [] = []
  mkRes {tys = (t :: ts)} (v :: vs) = (v ::: t) :: mkRes vs

{- Proof that a list of resources is a subset of another list -}
public export
data SubRes : Resources -> Resources -> Type where
     SubNil : SubRes [] []
     Skip : SubRes xs ys -> SubRes xs (y :: ys)
     InRes : (el : ElemRes x ys) -> SubRes xs (dropEl ys el) ->
              SubRes (x :: xs) ys

%hint
public export
subResId : SubRes xs xs
subResId {xs = []} = SubNil
subResId {xs = (x :: xs)} = InRes HereRes subResId

public export
subResNil : SubRes [] xs
subResNil {xs = []} = SubNil
subResNil {xs = (x :: xs)} = Skip subResNil

{- Proof that every variable in the list appears once in the context -}
public export
data VarsIn : List Var -> Resources -> Type where
     VarsNil : VarsIn [] []
     SkipVar : VarsIn xs ys -> VarsIn xs (y :: ys)
     InResVar : (el : VarInRes x ys) -> VarsIn xs (dropVarIn ys el) ->
                 VarsIn (x :: xs) ys

public export
Uninhabited (ElemRes x []) where
  uninhabited HereRes impossible
  uninhabited (ThereRes _) impossible

public export %error_reduce
updateWith : (new : Resources) -> (xs : Resources) ->
             SubRes ys xs -> Resources
-- At the end, add the ones which were updated by the subctxt
updateWith new [] SubNil = new
updateWith new [] (InRes el z) = absurd el
-- Don't add the ones which were consumed by the subctxt
updateWith [] (x :: xs) (InRes el p)
    = updateWith [] (dropEl _ el) p
-- A new item corresponding to an existing thing
updateWith (n :: ns) (x :: xs) (InRes el p)
    = n :: updateWith ns (dropEl _ el) p
updateWith new (x :: xs) (Skip p) = x :: updateWith new xs p

public export
getVarType : (xs : Resources) -> VarInRes v xs -> Type
getVarType ((MkRes v st) :: as) VarHere = st
getVarType (b :: as) (VarThere x) = getVarType as x

public export
getCombineType : VarsIn ys xs -> List Type
getCombineType VarsNil = []
getCombineType (InResVar el y) = getVarType _ el :: getCombineType y
getCombineType (SkipVar x) = getCombineType x

public export
dropCombined : VarsIn vs res -> Resources
dropCombined {res = []} VarsNil = []
dropCombined {res} (InResVar el y) = dropCombined y
dropCombined {res = (y :: ys)} (SkipVar x) = y :: dropCombined x

public export
combineVarsIn : (res : Resources) -> VarsIn (comp :: vs) res -> Resources
combineVarsIn {comp} res (InResVar el x)
     = ((comp ::: Composite (getCombineType x)) :: dropCombined (InResVar el x))
combineVarsIn (y :: ys) (SkipVar x) = y :: combineVarsIn ys x

namespace Env
  public export
  data Env : Resources -> Type where
       Nil : Env []
       (::) : ty -> Env xs -> Env ((lbl ::: ty) :: xs)

  (++) : Env xs -> Env ys -> Env (xs ++ ys)
  (++) [] ys = ys
  (++) (x :: xs) ys = x :: xs ++ ys

lookupEnv : InState lbl ty res -> Env res -> ty
lookupEnv Here (x :: xs) = x
lookupEnv (There p) (x :: xs) = lookupEnv p xs

updateEnv : (prf : InState lbl ty res) -> Env res -> ty' ->
            Env (updateRes res prf ty')
updateEnv Here (x :: xs) val = val :: xs
updateEnv (There p) (x :: xs) val = x :: updateEnv p xs val

dropVal : (prf : InState lbl st res) -> Env res -> Env (drop res prf)
dropVal Here (x :: xs) = xs
dropVal (There p) (x :: xs) = x :: dropVal p xs

envElem : ElemRes x xs -> Env xs -> Env [x]
envElem HereRes (x :: xs) = [x]
envElem (ThereRes p) (x :: xs) = envElem p xs

dropDups : Env xs -> (el : ElemRes x xs) -> Env (dropEl xs el)
dropDups (y :: ys) HereRes = ys
dropDups (y :: ys) (ThereRes p) = y :: dropDups ys p


dropEntry : Env res -> (prf : VarInRes x res) -> Env (dropVarIn res prf)
dropEntry (x :: env) VarHere = env
dropEntry (x :: env) (VarThere y) = x :: dropEntry env y

dropVarsIn : Env res -> (prf : VarsIn vs res) -> Env (dropCombined prf)
dropVarsIn [] VarsNil = []
dropVarsIn env (InResVar el z) = dropVarsIn (dropEntry env el) z
dropVarsIn (x :: env) (SkipVar z) = x :: dropVarsIn env z

getVarEntry : Env res -> (prf : VarInRes v res) -> getVarType res prf
getVarEntry (x :: xs) VarHere = x
getVarEntry (x :: env) (VarThere p) = getVarEntry env p

mkComposite : Env res -> (prf : VarsIn vs res) -> Composite (getCombineType prf)
mkComposite [] VarsNil = CompNil
mkComposite env (InResVar el z)
    = CompCons (getVarEntry env el) (mkComposite (dropEntry env el) z)
mkComposite (x :: env) (SkipVar z) = mkComposite env z

rebuildVarsIn : Env res -> (prf : VarsIn (comp :: vs) res) ->
                Env (combineVarsIn res prf)
rebuildVarsIn env (InResVar el p)
     = mkComposite (dropEntry env el) p :: dropVarsIn env (InResVar el p)
rebuildVarsIn (x :: env) (SkipVar p) = x :: rebuildVarsIn env p

{- Some things to make STrans interfaces look prettier -}

infix 6 :->

public export
data Action : Type -> Type where
     Stable : Var -> Type -> Action ty
     Trans : Var -> Type -> (ty -> Type) -> Action ty
     Remove : Var -> Type -> Action ty
     Add : (ty -> Resources) -> Action ty

namespace Stable
  public export %error_reduce
  (:::) : Var -> Type -> Action ty
  (:::) = Stable

namespace Trans
  public export
  data Trans ty = (:->) Type Type

  public export %error_reduce
  (:::) : Var -> Trans ty -> Action ty
  (:::) lbl (st :-> st') = Trans lbl st (const st')

namespace DepTrans
  public export
  data DepTrans ty = (:->) Type (ty -> Type)

  public export %error_reduce
  (:::) : Var -> DepTrans ty -> Action ty
  (:::) lbl (st :-> st') = Trans lbl st st'

public export
or : a -> a -> Either b c -> a
or x y = either (const x) (const y)

public export %error_reduce
add : Type -> Action Var
add ty = Add (\var => [var ::: ty])

public export %error_reduce
remove : Var -> Type -> Action ty
remove = Remove

public export %error_reduce
addIfRight : Type -> Action (Either a Var)
addIfRight ty = Add (either (const []) (\var => [var ::: ty]))

public export %error_reduce
addIfJust : Type -> Action (Maybe Var)
addIfJust ty = Add (maybe [] (\var => [var ::: ty]))

public export
kept : SubRes xs ys -> Resources
kept SubNil = []
kept (InRes el p) = kept p
kept (Skip {y} p) = y :: kept p

-- We can only use new/delete/read/write on things wrapped in State. Only an
-- interface implementation should know that a thing is defined as State,
-- so it's the only thing that's able to peek at the internals
public export
data State : Type -> Type where
     Value : ty -> State ty

export
data STrans : (m : Type -> Type) ->
              (ty : Type) ->
              Resources -> (ty -> Resources) ->
              Type where
     Pure : (result : ty) ->
            STrans m ty (out_fn result) out_fn
     Bind : STrans m a st1 st2_fn ->
            ((result : a) ->
                STrans m b (st2_fn result) st3_fn) ->
            STrans m b st1 st3_fn
     Lift : Monad m => m t -> STrans m t res (const res)
     RunAs : Applicative m => STrans m t in_res (const out_res) ->
             STrans m (m t) in_res (const out_res)

     New : (val : state) ->
           STrans m Var res (\lbl => (lbl ::: state) :: res)
     Delete : (lbl : Var) ->
              (prf : InState lbl st res) ->
              STrans m () res (const (drop res prf))
     DropSubRes : (prf : SubRes ys xs) ->
                  STrans m (Env ys) xs (const (kept prf))

     Split : (lbl : Var) ->
             (prf : InState lbl (Composite vars) res) ->
             STrans m (VarList vars) res
                   (\ vs => mkRes vs ++
                            updateRes res prf (State ()))
     Combine : (comp : Var) -> (vs : List Var) ->
               (prf : VarsIn (comp :: vs) res) ->
               STrans m () res
                   (const (combineVarsIn res prf))
     ToEnd : (lbl : Var) ->
             (prf : InState lbl state res) ->
             STrans m () res (const (drop res prf ++ [lbl ::: state]))

     Call : STrans m t sub new_f -> (res_prf : SubRes sub old) ->
            STrans m t old (\res => updateWith (new_f res) old res_prf)

     Read : (lbl : Var) ->
            (prf : InState lbl ty res) ->
            STrans m ty res (const res)
     Write : (lbl : Var) ->
             (prf : InState lbl ty res) ->
             (val : ty') ->
             STrans m () res (const (updateRes res prf ty'))

namespace Loop
  export
  data STransLoop : (m : Type -> Type) -> (ty : Type) ->
                    Resources -> (ty -> Resources) -> Type where
       Bind : STrans m a st1 st2_fn ->
              ((result : a) -> Inf (STransLoop m b (st2_fn result) st3_fn)) ->
              STransLoop m b st1 st3_fn
       Pure : (result : ty) -> STransLoop m ty (out_fn result) out_fn

export
dropEnv : Env ys -> SubRes xs ys -> Env xs
dropEnv [] SubNil = []
dropEnv [] (InRes idx rest) = absurd idx
dropEnv (z :: zs) (InRes idx rest)
    = let [e] = envElem idx (z :: zs) in
          e :: dropEnv (dropDups (z :: zs) idx) rest
dropEnv (z :: zs) (Skip p) = dropEnv zs p

keepEnv : Env ys -> (prf : SubRes xs ys) -> Env (kept prf)
keepEnv env SubNil = env
keepEnv env (InRes el prf) = keepEnv (dropDups env el) prf
keepEnv (z :: zs) (Skip prf) = z :: keepEnv zs prf

-- Corresponds pretty much exactly to 'updateWith'
rebuildEnv : Env new -> Env old -> (prf : SubRes sub old) ->
             Env (updateWith new old prf)
rebuildEnv new [] SubNil = new
rebuildEnv new [] (InRes el p) = absurd el
rebuildEnv [] (x :: xs) (InRes el p)
    = rebuildEnv [] (dropDups (x :: xs) el) p
rebuildEnv (e :: es) (x :: xs) (InRes el p)
    = e :: rebuildEnv es (dropDups (x :: xs) el) p
rebuildEnv new (x :: xs) (Skip p) = x :: rebuildEnv new xs p

runST : Env invars -> STrans m a invars outfn ->
        ((x : a) -> Env (outfn x) -> m b) -> m b
runST env (Pure result) k = k result env
runST env (Bind prog next) k
   = runST env prog (\prog', env' => runST env' (next prog') k)
runST env (Lift action) k
   = do res <- action
        k res env
runST env (RunAs prog) k = runST env prog (\res, env' => k (pure res) env')
runST env (New val) k = k MkVar (val :: env)
runST env (Delete lbl prf) k = k () (dropVal prf env)
runST env (DropSubRes prf) k = k (dropEnv env prf) (keepEnv env prf)
runST env (Split lbl prf) k = let val = lookupEnv prf env
                                  env' = updateEnv prf env (Value ()) in
                                  k (mkVars val) (addToEnv val env')
  where
    mkVars : Composite ts -> VarList ts
    mkVars CompNil = []
    mkVars (CompCons x xs) = MkVar :: mkVars xs

    addToEnv : (comp : Composite ts) -> Env xs -> Env (mkRes (mkVars comp) ++ xs)
    addToEnv CompNil env = env
    addToEnv (CompCons x xs) env = x :: addToEnv xs env
runST env (ToEnd var prf) k = k () (dropVal prf env ++ [lookupEnv prf env])
runST env (Combine lbl vs prf) k = k () (rebuildVarsIn env prf)
runST env (Call prog res_prf) k
   = let env' = dropEnv env res_prf in
         runST env' prog
                 (\prog', envk => k prog' (rebuildEnv envk env res_prf))
runST env (Read lbl prf) k = k (lookupEnv prf env) env
runST env (Write lbl prf val) k = k () (updateEnv prf env val)

export
data Fuel = Empty | More (Lazy Fuel)

export partial
forever : Fuel
forever = More forever

runSTLoop : Fuel -> Env invars -> STransLoop m a invars outfn ->
            (k : (x : a) -> Env (outfn x) -> m b) ->
            (onDry : m b) -> m b
runSTLoop Empty _ _ _ onDry = onDry
runSTLoop (More x) env (Bind prog next) k onDry
    = runST env prog (\prog', env' => runSTLoop x env' (next prog') k onDry)
runSTLoop (More x) env (Pure result) k onDry = k result env

export
pure : (result : ty) -> STrans m ty (out_fn result) out_fn
pure = Pure

export
(>>=) : STrans m a st1 st2_fn ->
        ((result : a) -> STrans m b (st2_fn result) st3_fn) ->
        STrans m b st1 st3_fn
(>>=) = Bind

export
returning : (result : ty) -> STrans m () res (const (out_fn result)) ->
            STrans m ty res out_fn
returning res prog = do prog
                        pure res


export
lift : Monad m => m t -> STrans m t res (const res)
lift = Lift

export
runAs : Applicative m => STrans m t in_res (const out_res) ->
        STrans m (m t) in_res (const out_res)
runAs = RunAs

export
new : (val : state) ->
      STrans m Var res (\lbl => (lbl ::: State state) :: res)
new val = New (Value val)

export
delete : (lbl : Var) ->
         {auto prf : InState lbl (State st) res} ->
         STrans m () res (const (drop res prf))
delete lbl {prf} = Delete lbl prf

-- Keep only a subset of the current set of resources. Returns the
-- environment corresponding to the dropped portion.
export
dropSub : {auto prf : SubRes ys xs} ->
          STrans m (Env ys) xs (const (kept prf))
dropSub {prf} = DropSubRes prf

export
split : (lbl : Var) ->
        {auto prf : InState lbl (Composite vars) res} ->
        STrans m (VarList vars) res
              (\ vs => mkRes vs ++
                       updateRes res prf (State ()))
split lbl {prf} = Split lbl prf

export
combine : (comp : Var) -> (vs : List Var) ->
          {auto prf : InState comp (State ()) res} ->
          {auto var_prf : VarsIn (comp :: vs) res} ->
          STrans m () res
              (const (combineVarsIn res var_prf))
combine comp vs {var_prf} = Combine comp vs var_prf

export
toEnd : (lbl : Var) ->
        {auto prf : InState lbl state res} ->
        STrans m () res (const (drop res prf ++ [lbl ::: state]))
toEnd lbl {prf} = ToEnd lbl prf

export -- implicit ???
call : STrans m t sub new_f ->
       {auto res_prf : SubRes sub old} ->
       STrans m t old (\res => updateWith (new_f res) old res_prf)
call prog {res_prf} = Call prog res_prf

export
read : (lbl : Var) ->
       {auto prf : InState lbl (State ty) res} ->
       STrans m ty res (const res)
read lbl {prf} = do Value x <- Read lbl prf
                    pure x

export
write : (lbl : Var) ->
        {auto prf : InState lbl ty res} ->
        (val : ty') ->
        STrans m () res (const (updateRes res prf (State ty')))
write lbl {prf} val = Write lbl prf (Value val)

export
update : (lbl : Var) ->
         {auto prf : InState lbl (State ty) res} ->
         (ty -> ty') ->
         STrans m () res (const (updateRes res prf (State ty')))
update lbl f = do x <- read lbl
                  write lbl (f x)

namespace Loop
   export
   (>>=) : STrans m a st1 st2_fn ->
          ((result : a) -> Inf (STransLoop m b (st2_fn result) st3_fn)) ->
          STransLoop m b st1 st3_fn
   (>>=) = Bind

   export
   pure : (result : ty) -> STransLoop m ty (out_fn result) out_fn
   pure = Pure

public export %error_reduce
out_res : ty -> (as : List (Action ty)) -> Resources
out_res x [] = []
out_res x ((Stable lbl inr) :: xs) = (lbl ::: inr) :: out_res x xs
out_res x ((Trans lbl inr outr) :: xs)
    = (lbl ::: outr x) :: out_res x xs
out_res x ((Remove lbl inr) :: xs) = out_res x xs
out_res x (Add outf :: xs) = outf x ++ out_res x xs

public export %error_reduce
in_res : (as : List (Action ty)) -> Resources
in_res [] = []
in_res ((Stable lbl inr) :: xs) = (lbl ::: inr) :: in_res xs
in_res ((Trans lbl inr outr) :: xs) = (lbl ::: inr) :: in_res xs
in_res ((Remove lbl inr) :: xs) = (lbl ::: inr) :: in_res xs
in_res (Add outf :: xs) = in_res xs

public export
%error_reduce -- always evaluate this before showing errors
ST : (m : Type -> Type) ->
     (ty : Type) ->
     List (Action ty) -> Type
ST m ty xs = STrans m ty (in_res xs) (\result : ty => out_res result xs)

public export
%error_reduce -- always evaluate this before showing errors
STLoop : (m : Type -> Type) ->
         (ty : Type) ->
         List (Action ty) -> Type
STLoop m ty xs = STransLoop m ty (in_res xs) (\result : ty => out_res result xs)

-- Console IO is useful sufficiently often that let's have it here
public export
interface ConsoleIO (m : Type -> Type) where
  putStr : String -> STrans m () xs (const xs)
  getStr : STrans m String xs (const xs)

  putChar : Char -> STrans m () xs (const xs)
  getChar : STrans m Char xs (const xs)


export
putStrLn : ConsoleIO m => String -> STrans m () xs (const xs)
putStrLn str = putStr (str ++ "\n")

export
print : (ConsoleIO m, Show a) => a -> STrans m () xs (const xs)
print a = putStr $ show a

export
printLn : (ConsoleIO m, Show a) => a -> STrans m () xs (const xs)
printLn a = putStrLn $ show a

export
ConsoleIO IO where
  putStr str = lift (Interactive.putStr str)
  getStr = lift Interactive.getLine

  putChar c = lift $ Interactive.putChar c
  getChar = lift Interactive.getChar

export
run : Applicative m => ST m a [] -> m a
run prog = runST [] prog (\res, env' => pure res)

export
runLoop : Applicative m => Fuel -> STLoop m a [] ->
          (onEmpty : m a) ->
          m a
runLoop fuel prog onEmpty
    = runSTLoop fuel [] prog (\res, env' => pure res) onEmpty

||| runWith allows running an STrans program with an initial environment,
||| which must be consumed.
||| It's only allowed in the IO monad, because it's inherently unsafe, so
||| we don't want to be able to use it under a 'lift' in just *any* ST program -
||| if we have access to an 'Env' we can easily duplicate it - so it's the
||| responsibility of an implementation of an interface in IO which uses it
||| to ensure that it isn't duplicated.
export
runWith : {resf : _} ->
          Env res -> STrans IO a res (\result => resf result) ->
          IO (result ** Env (resf result))
runWith env prog = runST env prog (\res, env' => pure (res ** env'))

export
runWithLoop : {resf : _} ->
          Env res -> Fuel -> STransLoop IO a res (\result => resf result) ->
          IO (Maybe (result ** Env (resf result)))
runWithLoop env fuel prog
    = runSTLoop fuel env prog (\res, env' => pure (Just (res ** env')))
                              (pure Nothing)

export
runPure : ST Basics.id a [] -> a
runPure prog = runST [] prog (\res, env' => res)

%language ErrorReflection

%error_handler
export
st_precondition : Err -> Maybe (List ErrorReportPart)
st_precondition (CantSolveGoal `(SubRes ~sub ~all) _)
   = pure
      [TextPart "'call' is not valid here. ",
       TextPart "The operation has preconditions ",
       TermPart sub,
       TextPart " which is not a sub set of ",
       TermPart all]
st_precondition (CantUnify _ tm1 tm2 _ _ _)
   = do reqPre <- getPreconditions tm1
        gotPre <- getPreconditions tm2
        reqPost <- getPostconditions tm1
        gotPost <- getPostconditions tm2
        pure $ [TextPart "Error in state transition:"] ++
                renderPre gotPre reqPre ++
                renderPost gotPost reqPost

  where
    getPreconditions : TT -> Maybe TT
    getPreconditions `(STrans ~m ~ret ~pre ~post) = Just pre
    getPreconditions `(STransLoop ~m ~ret ~pre ~post) = Just pre
    getPreconditions _ = Nothing

    getPostconditions : TT -> Maybe TT
    getPostconditions `(STrans ~m ~ret ~pre ~post) = Just post
    getPostconditions `(STransLoop ~m ~ret ~pre ~post) = Just post
    getPostconditions _ = Nothing

    renderPre : TT -> TT -> List (ErrorReportPart)
    renderPre got req
        = [SubReport [TextPart "Operation has preconditions: ",
                      TermPart req],
           SubReport [TextPart "States here are: ",
                      TermPart got]]
    renderPost : TT -> TT -> List (ErrorReportPart)
    renderPost got req
        = [SubReport [TextPart "Operation has postconditions: ",
                      TermPart req],
           SubReport [TextPart "Required result states here are: ",
                      TermPart got]]

st_precondition _ = Nothing

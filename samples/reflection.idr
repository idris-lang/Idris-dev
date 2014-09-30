module ReflectionExamples

import Language.Reflection

||| The reflected term for (\ x => reverse "bba")
reflectVal : TT
reflectVal = ?valPrf

||| intEq for the integers 3 and 3
applyTac1 : Int
applyTac1 = ?tacPrf1

||| intEq for the integers 3 and 42
applyTac0 : Int
applyTac0 = ?tacPrf0

||| intEq for the two arguments
applyTacDyn : Int -> Int -> Int
applyTacDyn x y = ?tacPrfDyn

||| Restored version for RConstant (I 42)
fill : Int
fill = ?fillPrf

||| The type (TTName, TT) computed from its reflected raw rep.
envTuple : Type
envTuple = ?envTuplePrf

||| The type List (TTName, TT) computed from its reflected raw rep.
envList : List (TTName, TT)
envList = ?envListPrf

||| Reflected raw rep. for the type (TTName, TT)
tupleType : Raw
tupleType = RApp (RApp (Var (UN "Pair"))
                       (Var (NS (UN "TTName") ["Reflection", "Language"])))
                 (Var (NS (UN "TT") ["Reflection", "Language"]))

||| Reflected raw rep for the type List (TTName, TT)
mkTuple : Raw
mkTuple = RApp (RApp (Var (UN "MkPair"))
                     (Var (NS (UN "TTName") ["Reflection", "Language"])))
               (Var (NS (UN "TT") ["Reflection", "Language"]))

||| Reflected raw rep for Prelude.List.Nil
nil : Raw
nil = (Var (NS (UN "Nil") ["List", "Prelude"]))

||| Reflected raw rep for Prelude.List.::
cons : Raw
cons = (Var (NS (UN "::") ["List", "Prelude"]))

||| 1 if the two arguments are equal, 0 otherwise
||| This function is chosen as simple as possible for
||| demo purposes.
intEq : Int -> Int -> Int
intEq x y = case x == y of
              True  => 1
              False => 0

||| A tactic script to run intEq on two let-bound or introduced
||| arguments of the current (otherwise empty) proof context
firstEq : List (TTName, Binder TT) -> TT -> Tactic
firstEq ((_, (Let _ y))::(_, (Let _ x))::(_, Let _ f)::Nil) _ = Exact (App (App f x) y)
firstEq ((y, Lam yt)::(x, Lam xt)::(_, Let _ f)::Nil) _ = Exact (App (App f (P (Bound) x xt)) (P Bound y yt))
firstEq xs _ = Exact (TConst (I 0))

||| Skip 1 argument of the proof context and return the second one which
||| has to be introduced. Used for the tactical dispatch example, which
||| will push dispatch, as first env agrument.
innerTac : List (TTName, Binder TT) -> TT -> Tactic
innerTac (_::(x, Lam xt)::_) _ = Exact (P Bound x xt)

||| Returns the reflected representation of innerTac
innerTacTT : TT
innerTacTT = ?innerTacTTPrf

||| Dispatch to the reflected rep. of innerTac
dispatch : List (TTName, Binder TT) -> TT -> Tactic
dispatch xs _ = ApplyTactic (innerTacTT)

||| Call dispatch which will then dispatch to innerTac.
tacticalDispatch : Int -> Int
tacticalDispatch = ?tacticalDispatchPrf

||| A tactic to get the representation of its goal
studyGoalTac : List (TTName, Binder TT) -> TT -> Tactic
studyGoalTac _ goal = Reflect goal

||| Returns the representation of its goal, TT
||| (so this is reflect on the type TT)
studyGoal : TT
studyGoal = ?studyGoalPrf

---------- Proofs ----------

ReflectionExamples.studyGoalPrf = proof {
  applyTactic studyGoalTac;
}

ReflectionExamples.envTuplePrf = proof {
  let x = tupleType;
  fill x;
}

ReflectionExamples.envListPrf = proof {
  let x : Raw = RApp nil tupleType;
  fill x;
}


ReflectionExamples.valPrf = proof {
  let x : (List String -> String) = (\ x => reverse "bba");
  reflect x;
}


ReflectionExamples.tacPrf1 = proof {
  let f : (Int -> Int -> Int) = intEq;
  let x : Int = 3;
  let y : Int = 3;
  applyTactic firstEq;
}

ReflectionExamples.tacPrf0 = proof {
  let f : (Int -> Int -> Int) = intEq;
  let x : Int = 3;
  let y : Int = 42;
  applyTactic firstEq;
}

ReflectionExamples.tacPrfDyn = proof {
  let f : (Int ->  Int -> Int) = intEq;
  intros;
  applyTactic firstEq;
}

ReflectionExamples.fillPrf = proof {
  let x : Raw = RConstant (I 42);
  fill x;
}

ReflectionExamples.innerTacTTPrf = proof {
  reflect innerTac;
}

ReflectionExamples.tacticalDispatchPrf = proof {
  intros;
  applyTactic dispatch;
}


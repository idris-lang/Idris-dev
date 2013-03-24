module Language.Reflection

%access public

data TTName = UN String
            -- ^ User-provided name
            | NS TTName (List String)
            -- ^ Root, namespaces
            | MN Int String
            -- ^ Machine chosen names
            | NErased
            -- ^ Name of somethng which is never used in scope

implicit
userSuppliedName : String -> TTName
userSuppliedName = UN

data TTUExp = UVar Int
            -- ^ universe variable
            | UVal Int
            -- ^ explicit universe variable

-- | Primitive constants
data Const = I Int | BI Nat | Fl Float | Ch Char | Str String
           | IType | BIType | FlType   | ChType  | StrType
           | B8 Bits8 | B16 Bits16 | B32 Bits32 | B64 Bits64
           | B8Type   | B16Type    | B32Type    | B64Type
           | PtrType | VoidType | Forgot

abstract class ReflConst (a : Type) where
   toConst : a -> Const

instance ReflConst Int where
   toConst x = I x

instance ReflConst Nat where
   toConst = BI

instance ReflConst Float where
   toConst = Fl

instance ReflConst Char where
   toConst = Ch

instance ReflConst String where
   toConst = Str

instance ReflConst Bits8 where
   toConst = B8

instance ReflConst Bits16 where
   toConst = B16

instance ReflConst Bits32 where
   toConst = B32

instance ReflConst Bits64 where
   toConst = B64

implicit
reflectConstant: (ReflConst a) => a -> Const
reflectConstant = toConst


-- | Types of named references
data NameType = Bound
              -- ^ reference which is just bound, e.g. by intro
              | Ref
              -- ^ reference to a variable
              | DCon Int Int
              -- ^ constructor with tag and number
              | TCon Int Int
              -- ^ type constructor with tag and number

-- | Types annotations for bound variables in different
-- binding contexts
data Binder a = Lam a
              | Pi a
              | Let a a
              | NLet a a
              | Hole a
              | GHole a
              | Guess a a
              | PVar a
              | PVTy a


instance Functor Binder where
  fmap f (Lam x) = Lam (f x)
  fmap f (Pi x) = Pi (f x)
  fmap f (Let x y) = Let (f x) (f y)
  fmap f (NLet x y) = NLet (f x) (f y)
  fmap f (Hole x) = Hole (f x)
  fmap f (GHole x) = GHole (f x)
  fmap f (Guess x y) = Guess (f x) (f y)
  fmap f (PVar x) = PVar (f x)
  fmap f (PVTy x) = PVTy (f x)

total
traverse : (Applicative f) =>  (a -> f b) -> Binder a -> f (Binder b)
traverse f (Lam x) = [| Lam (f x) |]
traverse f (Pi x) = [| Pi (f x) |]
traverse f (Let x y) = [| Let (f x) (f y) |]
traverse f (NLet x y) = [| NLet (f x) (f y) |]
traverse f (Hole x) = [| Hole (f x) |]
traverse f (GHole x) = [| GHole (f x) |]
traverse f (Guess x y) = [| Guess (f x) (f y) |]
traverse f (PVar x) = [| PVar (f x) |]
traverse f (PVTy x) = [| PVTy (f x) |]


-- | Reflection of the well typed core language
data TT = P NameType TTName TT
        -- ^ named binders
        | V Int
        -- ^ variables
        | Bind TTName (Binder TT) TT
        -- ^ type annotated named bindings
        | App TT TT
        -- ^ (named) application of a function to a value
        | TConst Const
        -- ^ constants
        | Proj TT Int
        -- ^ argument projection; runtime only
        | Erased
        -- ^ erased terms
        | Impossible
        -- ^ impossible terms
        | TType TTUExp
        -- ^ types

-- | Raw terms without types
data Raw = Var TTName
         | RBind TTName (Binder Raw) Raw
         | RApp Raw Raw
         | RType
         | RForce Raw
         | RConstant Const

data Tactic = Try Tactic Tactic
            -- ^ try the first tactic and resort to the second one on failure
            | GoalType String Tactic
            -- ^ only run if the goal has the right type
            | Refine TTName
            -- ^ resolve function name, find matching arguments in the
            -- context and compute the proof target
            | Seq Tactic Tactic
            -- ^ apply both tactics in sequence
            | Trivial
            -- ^ intelligently construct the proof target from the context
            | Solve
            -- ^ infer the proof target from the context
            | Intros
            -- ^ introduce all variables into the context
            | Intro TTName
            -- ^ introduce a named variable into the context, use the
            -- first one if the given name is not found
            | ApplyTactic TT
            -- ^ invoke the reflected rep. of another tactic
            | Reflect TT
            -- ^ turn a value into its reflected representation
            | Fill Raw
            -- ^ turn a raw value back into a term 
            | Exact TT
            -- ^ use the given value to conclude the proof
            | Focus TTName
            -- ^ focus a named hole
            | Rewrite TT
            -- ^ rewrite using the reflected rep. of a equality proof
            | LetTac TTName TT
            -- ^ name a reflected term
            | LetTacTy TTName TT TT
            -- ^ name a reflected term and type it
            | Compute
            -- ^ normalise the context


**********************
Core Language Features
**********************


-  Full-spectrum dependent types
-  Strict evaluation (plus ``Lazy : Type -> Type`` type constructor for
   explicit laziness)
-  Lambda, Pi (forall), Let bindings
-  Pattern matching definitions
-  Export modifiers ``public``, ``abstract``, ``private``
-  Function options ``partial``, ``total``
-  ``where`` clauses
-  "magic with"
-  Implicit arguments (in top level types)
-  "Bound" implicit arguments ``{n : Nat} -> {a : Type} -> Vect n a``
-  "Unbound" implicit arguments --- ``Vect n a`` is equivalent to the
   above in a type, ``n`` and ``a`` are implicitly bound. This applies
   to names beginning with a lower case letter in an argument position.
-  'Tactic' implicit arguments, which are solved by running a tactic
   script or giving a default argument, rather than by unification.
-  Unit type ``()``, empty type ``Void``
-  Tuples (desugaring to nested pairs)
-  Dependent pair syntax ``(x : T ** P x)`` (there exists an ``x`` of
   type ``T`` such that ``P x``)
-  Inline ``case`` expressions
-  Heterogeneous equality
-  ``do`` notation
-  Idiom brackets
-  Interfaces (like type classes), supporting default methods and dependencies between
   methods
-  ``rewrite`` prf ``in`` expr
-  Metavariables
-  Inline proof/tactic scripts
-  Implicit coercion
-  ``codata``
-  Also ``Inf : Type -> Type`` type constructor for mixed data/codata.
   In fact ``codata`` is implemented by putting recursive arguments under
   ``Inf``.
-  ``syntax`` rules for defining pattern and term syntactic sugar
-  these are used in the standard library to define
   ``if ... then ... else`` expressions and an Agda-style preorder
   reasoning syntax.
-  `Uniqueness
   typing <https://github.com/idris-lang/Idris-dev/wiki/Uniqueness-Types>`__
   using the ``UniqueType`` universe.
-  `Partial
   evaluation <https://github.com/idris-lang/Idris-dev/wiki/Static-Arguments-and-Partial-Evaluation>`__
   by ``%static`` argument annotations.
-  Error message reflection
-  Eliminators
-  Label types ``'name``
-  ``%logging n``
-  ``%unifyLog``

Primitive Operators
===================

.. list-table::
   :widths: 10 30
   :stub-columns: 1

   * - gensym
     - Generate a unique name based on some hint.

       Useful when establishing a new binder.

       **NB**: the generated name is unique **for this run of the elaborator**.

       Do not assume that they are globally unique.

       Signature:

       gensym : (hint : String) -> Elab TTName

   * - solve
     - Substitute a guess into a hole.


       .. image:: ../image/solve.png
          :width: 141px
          :height: 74px
          :alt: diagram illustrating solve tactic


       Substitute the focused guess throughout its scope, eliminating it and moving focus to the next element of the hole queue. Fail if the focus is not a guess.

       Signature:

       solve : Elab ()

        Example:

        .. code-block:: idris

          %language ElabReflection

          testFn : Nat
          testFn = %runElab (do fill `(Z)
                                solve)

   * - fill
     -  Place a term into a hole, unifying its type. Fails if the focus is not a hole.


        .. image:: ../image/fill.png
           :width: 140px
           :height: 74px
           :alt: diagram illustrating fill tactic


        Signature:

        fill : (e : Raw) -> Elab ()

        Place a term e with type tc into the focused hole:

        ?h : th.e'

        and convert it to a guess:

        ?h ≈ e:t.e'

        and fail if the current focus is not a hole. The type t of the  guess is constructed by unifying tc and th, which may instantiate holes that they refer to. Fail if the current focus is not a hole or if unification fails.

        This unification can result in the solution of further holes or the establishment of additional unsolved unification constraints.

        Example:

        .. code-block:: idris

          %language ElabReflection

          testFn : Nat
          testFn = %runElab (do fill `(Z)
                                solve)

   * - apply
     - Attempt to apply an operator to fill the current hole, potentially solving arguments by unification.

       A hole is established for each argument.

       The return value is the list of holes established for the arguments to the function.

       Note that not all of the returned hole names still exist, as they may have been solved.

       - @ op the term to apply
       - @ argSpec - A list of booleans, one for each argument that the operator will be applied to. If true then attempt to solve the argument by unification.

       Signature:

       apply : (op : Raw) -> (argSpec : List Bool) -> Elab (List TTName)

       Example: elaborating an application of a function f that takes one implicit and two explicit arguments might invoke:

       apply \`(f) [False, True, True]

       Here is an example of an elab script that uses apply to insert the term plus Z (S Z) into a goal of type Nat.

       .. code-block:: idris

         do [x,y] <- apply `(plus) [False, False] 
         solve
         focus x; fill `(Z); solve
         focus y; fill `(S Z); solve

       The names of the established holes are returned.

       Note: This was added to the original tactic language to allow elaborator reflection.

   * - matchApply
     - Attempt to apply an operator to fill the current hole, potentially solving arguments by matching.

       The return value is the list of holes established for the arguments to the function.

       Note that not all of the returned hole names still exist, as they may have been solved.

       - @ op the term to apply
       - @ argSpec instructions for finding the arguments to the term, where the Boolean states whether or not to attempt to solve the argument by matching.

       Signature:

       matchApply : (op : Raw) -> (argSpec : List Bool) -> Elab (List TTName)

   * - focus
     - Move the focus to the specified hole, bringing it to the front of the hole queue. Fails if the hole does not exist.

       @ hole the hole to focus on

       Signature:

       focus : (hole : TTName) -> Elab ()

   * - unfocus
     - Send the currently-focused hole to the end of the hole queue and focus on the next hole.

       Signature:

       unfocus : TTName -> Elab ()

   * - attack
     - Convert a hole to make it suitable for bindings.


       .. image:: ../image/attack.png
          :width: 152px
          :height: 70px
          :alt: diagram illustrating attack tactic


       The binding tactics require that a hole be directly under its binding, or else the scopes of the generated terms won't make sense. This tactic creates a new hole of the proper form, and points the old hole at it.

       Signature:

       attack : Elab ()

   * - claim
     - Establish a new hole binding named n with type t, surrounding the current focus.

       Introduce a new hole with a specified name and type.

       The new hole will be focused, and the previously-focused hole will be immediately after it in the hole queue. Because this tactic introduces a new binding, you may need to 'attack' first.

       Signature:

       claim : TTName -> Raw -> Elab ()

   * - patvar
     - Convert a hole into a pattern variable.

       Signature:

       patvar : TTName -> Elab ()

   * - compute
     - Normalise the goal.

       Often this is not necessary because normanisation is applied during other tactics.

       Signature:

       compute : Elab ()

   * - normalise
     - Normalise a term in some lexical environment

       - @ env the environment in which to compute (get one of these from `getEnv`)
       - @ term the term to normalise

       Signature:

       normalise : (env : List (TTName, Binder TT)) -> (term : TT) -> Elab TT

   * - whnf
     - Reduce a closed term to weak-head normal form

       @ term the term to reduce

       Signature:

       whnf : (term : TT) -> Elab TT

   * - convertsInEnv
     - Check that two terms are convertible in the current context and in some environment.

       - @ env a lexical environment to compare the terms in (see `getEnv`)
       - @ term1 the first term to convert
       - @ term2 the second term to convert

       Signature:

       convertsInEnv : (env : List (TTName, Binder TT)) -> (term1, term2 : TT) -> Elab ()

   * - converts
     - Check that two terms are convertable in the current context and environment

       - @ term1 the first term to convert
       - @ term2 the second term to convertconverts : (term1, term2 : TT) -> Elab ()

       converts term1 term2 = convertsInEnv !getEnv term1 term2

   * - getSourceLocation
     - Find the source context for the elaboration script

       Signature:

       getSourceLocation : Elab SourceLocation

   * - sourceLocation
     - Attempt to solve the current goal with the source code

       locationsourceLocation : Elab ()

       .. code-block:: idris

         sourceLocation = do loc <- getSourceLocation
           fill (quote loc)
           solve

   * - currentNamespace
     - Get the current namespace at the point of tactic execution. This allows scripts to define top-level names conveniently.

       The namespace is represented as a reverse-order list of strings, just as in the representation of names.

       Signature:

       currentNamespace : Elab (List String)

   * - rewriteWith
     - Attempt to rewrite the goal using an equality.

       The tactic searches the goal for applicable subterms, and constructs a context for `replace` using them. In some cases, this is not possible, and `replace` must be called manually with an appropriate context.

       Because this tactic internally introduces a `let` binding, it requires that the hole be immediately under its binder (use 'attack' if it might not be).

       Signature:

       rewriteWith : Raw -> Elab ()

   * - resolveTC
     - Attempt to solve the current goal with an interface dictionary

       @ fn the name of the definition being elaborated (to prevent Idris from looping)

       Signature:

       resolveTC : (fn : TTName) -> Elab ()

   * - search
     - Use Idris's internal proof search.

       Signature:

       search : Elab ()

   * - search'
     - Use Idris's internal proof search, with more control.

       - @ depth the search depth
       - @ hints additional names to try

       Signature:

       search' : (depth : Int) -> (hints : List TTName) -> Elab ()

   * - operatorFixity
     - Look up the declared fixity for an operator.

       The lookup fails if the operator does not yet have a fixity or if the string is not a valid operator.

       @ operator the operator string to look up

       Signature:

       operatorFixity : (operator : String) -> Elab Fixity

   * - debug
     - Halt elaboration, dumping the internal state for inspection.

       This is intended for elaboration script developers, not for end-users. Use `fail` for final scripts.

       Signature:

       debug : Elab a

       If 'debug' is not the last tactic then make sure its type is sufficiently constrained. In particular, its type is Elab a, but there's no way for Idris to find out which type was meant for a. This can be fixed by either writing an explicit type (e.g. debug {a = ()}) or by using a helper that constrains the type (such as simple in Pruviloj, e.g. simple debug as a line).

       .. code-block:: idris

         %language ElabReflection

         idNat : Nat -> Nat
         idNat = %runElab (do intro `{{x}}
                              debug {a = ()}
                              fill (Var `{{x}})
                              solve)

   * - debugMessage
     - Halt elaboration, dumping the internal state and displaying a message.

       This is intended for elaboration script developers, not for end-users. Use `fail` for final scripts.

       @ msg the message to display

       Signature:

       debugMessage : (msg : List ErrorReportPart) -> Elab a 

       If 'debugMessage' is not the last tactic then make sure its type is sufficiently constrained. In particular, its type is Elab a, but there's no way for Idris to find out which type was meant for a. This can be fixed by either writing an explicit type (e.g. debugMessage [TextPart "message"] {a = ()}) or by using a helper that constrains the type (such as simple in Pruviloj, e.g. simple debug as a line).

       .. code-block:: idris

          %language ElabReflection
          idNat : Nat -> Nat
          idNat = %runElab (do intro `{{x}}
                               debugMessage [TextPart "error message"] {a = ()}
                               fill (Var `{{x}})
                               solve)

   * - metavar
     - Create a new top-level metavariable to solve the current hole.

       @ name the name for the top-level variable

       Signature:

       metavar : (name : TTName) -> Elab ()

   * - runElab
     - Recursively invoke the reflected elaborator with some goal.

       The result is the final term and its type.

       Signature:

       runElab : Raw -> Elab () -> Elab (TT, TT)


Read and Write State
--------------------

.. list-table::
   :widths: 10 30
   :stub-columns: 1

   * - getEnv
     - Look up the lexical binding at the focused hole. Fails if no holes are present.

       Signature:

       getEnv : Elab (List (TTName, Binder TT))

   * - getGoal
     - Get the name and type of the focused hole. Fails if not holes are present.

       Signature:

       getGoal : Elab (TTName, TT)

   * - getHoles
     - Get the hole queue, in order.

       Signature:

       getHoles : Elab (List TTName)

   * - getGuess
     - If the current hole contains a guess, return it. Otherwise, fail. 

       Signature:

       getGuess : Elab TT

   * - lookupTy
     - Look up the types of every overloading of a name.

       Signature:

       lookupTy :  TTName -> Elab (List (TTName, NameType, TT))

   * - lookupTyExact
     - Get the type of a fully-qualified name. Fail if it doesn't  resolve uniquely. 

       Signature:

       lookupTyExact : TTName -> Elab (TTName, NameType, TT)

   * - lookupDatatype
     - Find the reflected representation of all datatypes whose names are overloadings of some name.

       Signature:

       lookupDatatype : TTName -> Elab (List Datatype)

   * - lookupDatatypeExact
     - Find the reflected representation of a datatype, given its fully-qualified name. Fail if the name does not uniquely resolve to a datatype.

       Signature:

       lookupDatatypeExact : TTName -> Elab Datatype

   * - lookupFunDefn
     - Find the reflected function definition of all functions whose names are overloadings of some name.

       Signature:

       lookupFunDefn : TTName -> Elab (List (FunDefn TT))

   * - lookupFunDefnExact
     - Find the reflected function definition of a function, given its fully-qualified name. Fail if the name does not uniquely resolve to a function.

       Signature:

       lookupFunDefnExact : TTName -> Elab (FunDefn TT)

   * - lookupArgs
     - Get the argument specification for each overloading of a name.

       Signature:

       lookupArgs : TTName -> Elab (List (TTName, List FunArg, Raw))

   * - lookupArgsExact
     - Get the argument specification for a name. Fail if the name does not uniquely resolve.

       Signature:

       lookupArgsExact : TTName -> Elab (TTName, List FunArg, Raw)

   * - check
     - Attempt to type-check a term, getting back itself and its type.

       - @ env the environment within which to check the type
       - @ tm the term to check

       Signature:

       check : (env : List (TTName, Binder TT)) -> (tm : Raw) -> Elab (TT, TT)

Error Handling
--------------

.. list-table::
   :widths: 10 30
   :stub-columns: 1

   * - tryCatch
     - `tryCatch t (\err => t')` will run `t`, and if it fails, roll back the elaboration state and run `t'`,
       but with access to the knowledge of why `t` failed.

       Signature:

       tryCatch : Elab a -> (Err -> Elab a) -> Elab a

       .. code-block:: idris

         %language ElabReflection

         f : Err -> Elab ()
         f (Msg _) = fill `("message error")
         f (CantUnify _ _ _ _ _ _) = fill `("unification error")
         f _ = fill `("other")

         s2 : String
         s2 = %runElab (do tryCatch (fill `(True)) f ; solve)

   * - fail
     - Halt elaboration with an error

       Signature:

       fail : List ErrorReportPart -> Elab a

       Note: we may need to make sure the return type 'a' is sufficiently constrained. If required add an explicit type {a = ()}.

       Below is some code which includes 'fail'. This will always fail but we could replace 'True' with some more useful condition.

       .. code-block:: idris

         %language ElabReflection

         id1 : Elab ()
         id1 = do
           intro `{{x}}
           fill (Var `{{x}})
           if True
             then
               fail [TextPart "put error message here"]
             else
               solve

         idNat : Nat -> Nat
         idNat = %runElab id1

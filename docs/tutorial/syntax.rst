.. _sect-syntax:

*****************
Syntax Extensions
*****************

Idris supports the implementation of *Embedded Domain Specific
Languages* (EDSLs) in several ways [1]_. One way, as we have already
seen, is through extending ``do`` notation. Another important way is
to allow extension of the core syntax. In this section we describe two
ways of extending the syntax: ``syntax`` rules and ``dsl`` notation.

``syntax`` rules
================

We have seen ``if...then...else`` expressions, but these are not built
in. Instead, we can define a function in the prelude as follows (we
have already seen this function in Section :ref:`sect-lazy`):

.. code-block:: idris

    ifThenElse : (x:Bool) -> Lazy a -> Lazy a -> a;
    ifThenElse True  t e = t;
    ifThenElse False t e = e;

and then extend the core syntax with a ``syntax`` declaration:

.. code-block:: idris

    syntax if [test] then [t] else [e] = ifThenElse test t e;

The left hand side of a ``syntax`` declaration describes the syntax
rule, and the right hand side describes its expansion. The syntax rule
itself consists of:

-  **Keywords** — here, ``if``, ``then`` and ``else``, which must be
   valid identifiers.

-  **Non-terminals** — included in square brackets, ``[test]``, ``[t]``
   and ``[e]`` here, which stand for arbitrary expressions. To avoid
   parsing ambiguities, these expressions cannot use syntax extensions
   at the top level (though they can be used in parentheses).

-  **Names** — included in braces, which stand for names which may be
   bound on the right hand side.

-  **Symbols** — included in quotations marks, e.g. ``":="``. This can
   also be used to include reserved words in syntax rules, such as
   ``"let"`` or ``"in"``.

The limitations on the form of a syntax rule are that it must include
at least one symbol or keyword, and there must be no repeated
variables standing for non-terminals. Any expression can be used, but
if there are two non-terminals in a row in a rule, only simple
expressions may be used (that is, variables, constants, or bracketed
expressions). Rules can use previously defined rules, but may not be
recursive. The following syntax extensions would therefore be valid:

.. code-block:: idris

    syntax [var] ":=" [val]                = Assign var val;
    syntax [test] "?" [t] ":" [e]          = if test then t else e;
    syntax select [x] from [t] "where" [w] = SelectWhere x t w;
    syntax select [x] from [t]             = Select x t;

Syntax macros can be further restricted to apply only in patterns (i.e.
only on the left hand side of a pattern match clause) or only in terms
(i.e. everywhere but the left hand side of a pattern match clause) by
being marked as ``pattern`` or ``term`` syntax rules. For example, we
might define an interval as follows, with a static check that the lower
bound is below the upper bound using ``so``:

.. code-block:: idris

    data Interval : Type where
       MkInterval : (lower : Double) -> (upper : Double) ->
                    So (lower < upper) -> Interval

We can define a syntax which, in patterns, always matches ``Oh`` for
the proof argument, and in terms requires a proof term to be provided:

.. code-block:: idris

    pattern syntax "[" [x] "..." [y] "]" = MkInterval x y Oh
    term    syntax "[" [x] "..." [y] "]" = MkInterval x y ?bounds_lemma

In terms, the syntax ``[x...y]`` will generate a proof obligation
``bounds_lemma`` (possibly renamed).

Finally, syntax rules may be used to introduce alternative binding
forms. For example, a ``for`` loop binds a variable on each iteration:

.. code-block:: idris

    syntax for {x} "in" [xs] ":" [body] = forLoop xs (\x => body)

    main : IO ()
    main = do for x in [1..10]:
                  putStrLn ("Number " ++ show x)
              putStrLn "Done!"

Note that we have used the ``{x}`` form to state that ``x`` represents
a bound variable, substituted on the right hand side. We have also put
``in`` in quotation marks since it is already a reserved word.

``dsl`` notation
================

The well-typed interpreter in Section :ref:`sect-interp` is a simple
example of a common programming pattern with dependent types. Namely:
describe an *object language* and its type system with dependent types
to guarantee that only well-typed programs can be represented, then
program using that representation. Using this approach we can, for
example, write programs for serialising binary data [2]_ or running
concurrent processes safely [3]_.

Unfortunately, the form of object language programs makes it rather
hard to program this way in practice. Recall the factorial program in
``Expr`` for example:

.. code-block:: idris

    fact : Expr G (TyFun TyInt TyInt)
    fact = Lam (If (Op (==) (Var Stop) (Val 0))
                   (Val 1) (Op (*) (App fact (Op (-) (Var Stop) (Val 1)))
                                   (Var Stop)))

Since this is a particularly useful pattern, Idris provides syntax
overloading [1]_ to make it easier to program in such object
languages:

.. code-block:: idris

    mkLam : TTName -> Expr (t::g) t' -> Expr g (TyFun t t')
    mkLam _ body = Lam body

    dsl expr
        variable    = Var
        index_first = Stop
        index_next  = Pop
        lambda      = mkLam

A ``dsl`` block describes how each syntactic construct is represented
in an object language. Here, in the ``expr`` language, any variable is
translated to the ``Var`` constructor, using ``Pop`` and ``Stop`` to
construct the de Bruijn index (i.e., to count how many bindings since
the variable itself was bound); and any lambda is translated to a
``Lam`` constructor. The ``mkLam`` function simply ignores its first
argument, which is the name that the user chose for the variable. It
is also possible to overload ``let`` and dependent function syntax
(``pi``) in this way. We can now write ``fact`` as follows:

.. code-block:: idris

    fact : Expr G (TyFun TyInt TyInt)
    fact = expr (\x => If (Op (==) x (Val 0))
                          (Val 1) (Op (*) (app fact (Op (-) x (Val 1))) x))

In this new version, ``expr`` declares that the next expression will
be overloaded. We can take this further, using idiom brackets, by
declaring:

.. code-block:: idris

    (<*>) : (f : Lazy (Expr G (TyFun a t))) -> Expr G a -> Expr G t
    (<*>) f a = App f a

    pure : Expr G a -> Expr G a
    pure = id

Note that there is no need for these to be part of an implementation of
``Applicative``, since idiom bracket notation translates directly to
the names ``<*>`` and ``pure``, and ad-hoc type-directed overloading
is allowed. We can now say:

.. code-block:: idris

    fact : Expr G (TyFun TyInt TyInt)
    fact = expr (\x => If (Op (==) x (Val 0))
                          (Val 1) (Op (*) [| fact (Op (-) x (Val 1)) |] x))

With some more ad-hoc overloading and use of interfaces, and a new
syntax rule, we can even go as far as:

.. code-block:: idris

    syntax "IF" [x] "THEN" [t] "ELSE" [e] = If x t e

    fact : Expr G (TyFun TyInt TyInt)
    fact = expr (\x => IF x == 0 THEN 1 ELSE [| fact (x - 1) |] * x)


.. [1] Edwin Brady and Kevin Hammond. 2012. Resource-Safe systems
       programming with embedded domain specific languages. In
       Proceedings of the 14th international conference on Practical
       Aspects of Declarative Languages (PADL'12), Claudio Russo and
       Neng-Fa Zhou (Eds.). Springer-Verlag, Berlin, Heidelberg,
       242-257. DOI=10.1007/978-3-642-27694-1_18
       http://dx.doi.org/10.1007/978-3-642-27694-1_18

.. [2] Edwin C. Brady. 2011. IDRIS ---: systems programming meets full
       dependent types. In Proceedings of the 5th ACM workshop on
       Programming languages meets program verification (PLPV
       '11). ACM, New York, NY, USA,
       43-54. DOI=10.1145/1929529.1929536
       http://doi.acm.org/10.1145/1929529.1929536

.. [3] Edwin Brady and Kevin Hammond. 2010. Correct-by-Construction
       Concurrency: Using Dependent Types to Verify Implementations of
       Effectful Resource Usage Protocols. Fundam. Inf. 102, 2 (April
       2010), 145-176. http://dl.acm.org/citation.cfm?id=1883636

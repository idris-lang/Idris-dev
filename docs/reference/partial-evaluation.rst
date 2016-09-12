****************************************
Static Arguments and Partial Evaluation
****************************************

As of version 0.9.15, Idris has support for *partial evaluation* of
statically known arguments. This involves creating specialised versions
of functions with arguments annotated as ``[static]``.

(This is an implementation of the partial evaluator described in `this
ICFP 2010
paper <http://eb.host.cs.st-andrews.ac.uk/writings/icfp10.pdf>`__.
Please refer to this for more precise definitions of what follows.)

Partial evaluation is switched on by default. It can be disabled with
the ``--no-partial-eval`` flag.

Introductory Example
--------------------

Consider the power function over natural numbers, defined as follows
(we'll call it ``my_pow`` since ``pow`` already exists in the Prelude):

::

    my_pow : Nat -> Nat -> Nat
    my_pow x Z = 1
    my_pow x (S k) = mult x (my_pow x k)

This is implemented by recursion on the second argument, and we can
evaluate the definition further if the second argument is known, even if
the first isn't. For example, we can build a function at the REPL to
cube a number as follows:

::

    *pow> \x => my_pow x 3
    \x => mult x (mult x (mult x 1)) : Nat -> Nat
    *pow> it 3
    27 : Nat

Note that in the resulting function the recursion has been eliminated,
since ``my_pow`` is implemented by recursion on the known argument. We
have no such luck if the first argument is known and the second isn't:

::

    *pow> \x => my_pow 2 x
    \x => my_pow 2 x : Nat -> Nat

Now, consider the following definition which calculates x^2 + 1:

::

    powFn : Nat -> Nat
    powFn x = plus (my_pow x (S (S Z))) (S Z)

Since the second argument to ``my_pow`` here is statically known, it
seems a shame to have to make the recursive calls every time. However,
Idris will not in general inline recursive definitions, in particular
since they may diverge or duplicate work without some deeper analysis.

We can, however, give Idris some hints that here we really would like to
create a specialised version of ``my_pow``.

Automatic specialisation of ``pow``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The trick is to mark the statically known arguments with the
``[static]`` flag:

::

    my_pow : Nat -> [static] Nat -> Nat
    my_pow k Z = 1
    my_pow k (S j) = mult k (my_pow k j)

When an argument is annotated in this way, Idris will try to create a
specialised version whenever it accounts a call with a concrete value
(i.e. a constant, constructor form, or globally defined function) in a
``[static]`` position. If ``my_pow`` is defined this way, and ``powFn``
defined as above, we can see the effect by typing ``:printdef powFn`` at
the REPL:

::

    *pow> :printdef powFn
    powFn : Nat -> Nat
    powFn x = plus (PE_my_pow_3f3e5ad8 x) 1

What is this mysterious ``PE_my_pow_3f3e5ad8``? It's a specialised power
function where the statically known argument has been specialised away.
The name is generated from a hash of the specialised arguments, and we
can see its definition with ``:printdef`` too:

::

    *petest> :printdef PE_my_pow_3f3e5ad8
    PE_my_pow_3f3e5ad8 : Nat -> Nat
    PE_my_pow_3f3e5ad8 (0arg) = mult (0arg) (mult (0arg) (PE_fromInteger_7ba9767f 1))

The ``(0arg)`` is an internal argument name (programmers can't give
variable names beginning with a digit after all). Notice also that there
is a specialised version of ``fromInteger`` for ``Nat``\ s, since type
class dictionaries are themselves a particularly common case of
statically known arguments!

Specialising Type Classes
-------------------------

Type class dictionaries are very often statically known, so Idris
automatically marks any type class constraint as ``[static]`` and builds
specialised versions of top level functions where the class is
instantiated. For example, given:

::

    calc : Int -> Int
    calc x = (x * x) + x

If we print this definition, we'll see a specialised version of ``+`` is
used:

::

    *petest> :printdef calc
    calc : Int -> Int
    calc x = PE_+_954510b4 (PE_*_954510b4 x x) x

More interestingly, consider ``vadd`` which adds corresponding elements
in a vector of anything numeric:

::

    vadd : Num a => Vect n a -> Vect n a -> Vect n a
    vadd [] [] = []
    vadd (x :: xs) (y :: ys) = x + y :: vadd xs ys

If we use this on something concrete as follows...

::

    test : List Int -> List Int
    test xs = let xs' = fromList xs in
                  toList $ vadd xs' xs'

...then in fact, we get a specialised version of ``vadd`` in the
definition of ``test``, and indeed the specialised version of
``toList``:

::

    test : List Int -> List Int
    test xs = let xs' = fromList xs
              in PE_toList_888ae67 (PE_vadd_33f98d3d xs' xs')

Here's the specialised version of ``vadd``:

::

    PE_vadd_33f98d3d : Vect n Int -> Vect n Int -> Vect n Int
    PE_vadd_33f98d3d [] [] = []
    PE_vadd_33f98d3d (x :: xs) (y :: ys) = ((PE_+_954510b4 x y) ::
                                           (PE_vadd_33f98d3d xs ys))

Note that the recursive structure has been preserved, and the recursive
call to ``vadd`` has been replaced with a recursive call to the
specialised version. We've also got the same specialised version of
``+`` that we had above in ``calc``.

Specialising Higher Order Functions
-----------------------------------

Another case where partial evaluation can be useful is in automatically
making specialised versions of higher order functions. Unlike type class
dictionaries, this is not done automatically, but we might consider
writing ``map`` as follows:

::

    my_map : [static] (a -> b) -> List a -> List b
    my_map f [] = []
    my_map f (x :: xs) = f x :: my_map f xs

Then using ``my_map`` will yield specialised versions, for example to
double every value in a list of ``Int``\ s we could write:

::

    doubleAll : List Int -> List Int
    doubleAll xs = my_map (*2) xs

This would yield a specialised version of ``my_map``, used in
``doubleAll`` as follows:

::

    doubleAll : List Int -> List Int
    doubleAll xs = PE_my_map_1f8225c4 xs

    PE_my_map_1f8225c4 : List Int -> List Int
    PE_my_map_1f8225c4 [] = []
    PE_my_map_1f8225c4 (x :: xs) = ((PE_*_954510b4 x 2) :: (PE_my_map_1f8225c4 xs))

Specialising Interpreters
-------------------------

A particularly useful situation where partial evaluation becomes
effective is in defining an interpreter for a well-typed expression
language, defined as follows (see the `Idris tutorial, section
4 <http://eb.host.cs.st-andrews.ac.uk/writings/idris-tutorial.pdf>`__
for more details on how this works):

::

    data Expr : Vect n Ty -> Ty -> Type where
         Var : HasType i gamma t -> Expr gamma t
         Val : (x : Int) -> Expr gamma TyInt
         Lam : Expr (a :: gamma) t -> Expr gamma (TyFun a t)
         App : Lazy (Expr gamma (TyFun a t)) -> Expr gamma a -> Expr gamma t
         Op  : (interpTy a -> interpTy b -> interpTy c) -> Expr gamma a -> Expr gamma
               Expr gamma c
         If  : Expr gamma TyBool -> Expr gamma a -> Expr gamma a -> Expr gamma a

    dsl expr
        lambda = Lam
        variable = Var
        index_first = stop
        index_next = pop

We can write a couple of test functions in this language as follows,
using the ``dsl`` notation to overload lambdas; first a function which
multiplies two inputs:

::

    eMult : Expr gamma (TyFun TyInt (TyFun TyInt TyInt))
    eMult = expr (\x, y => Op (*) x y)

Then, a function which calculates the factorial of its input:

::

    eFac : Expr gamma (TyFun TyInt TyInt)
    eFac = expr (\x => If (Op (==) x (Val 0))
                (Val 1)
                (App (App eMult (App eFac (Op (-) x (Val 1)))) x))

The interpreter's type is written as follows, marking the expression to
be evaluated as ``[static]``:

::

    interp : (env : Env gamma) -> [static] (e : Expr gamma t) -> interpTy t

This means that if we write an Idris program to calculate a factorial by
calling ``interp`` on ``eFac``, the resulting definition will be
specialised, partially evaluating away the interpreter:

::

    runFac : Int -> Int
    runFac x = interp [] eFac x

We can see that the call to ``interp`` has been partially evaluated away
as follows:

::

    *interp> :printdef runFac
    runFac : Int -> Int
    runFac x = PE_interp_ed1429e [] x

If we look at ``PE_interp_ed1429e`` we'll see that it follows exactly
the structur of ``eFac``, with the interpreter evaluated away:

::

    *interp> :printdef PE_interp_ed1429e
    PE_interp_ed1429e : Env gamma -> Int -> Int
    PE_interp_ed1429e (3arg) = \x =>
                                 boolElim (x == 0)
                                          (Delay 1)
                                          (Delay (PE_interp_b5c2d0ff (x :: (3arg))
                                                                     (PE_interp_ed1429e (x :: (3arg)) (x - 1)) x))


For the sake of readability, I have simplified this slightly: what you
will really see also includes specialised versions of ``==``, ``-`` and
``fromInteger``. Note that ``PE_interp_ed1429e``, which represents
``eFac`` has become a recursive function following the structure of
``eFac``. There is also a call to ``PE_interp_b5c2d0ff`` which is a
specialised interpeter for ``eMult``.

These definitions arise because the partial evaluator will only
specialise a definition by a specific concrete argument once, then it is
cached for future use. So any future applications of ``interp`` on
``eFac`` will also be translated to ``PE_interp_ed1429e``.

The specialised version of ``eMult``, without any simplification for
readability, is:

::

    PE_interp_b5c2d0ff : Env gamma -> Int -> Int -> Int
    PE_interp_b5c2d0ff (3arg) = \x => \x1 => PE_*_954510b4 x x1

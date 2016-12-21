.. _sect-documenting:

**********************
Documenting Idris Code
**********************

Idris documentation comes in two major forms: comments, which exist
for a reader’s edification and are ignored by the compiler, and inline
API documentation, which the compiler parses and stores for future
reference. To consult the documentation for a declaration ``f``, write
``:doc f`` at the REPL or use the appropriate command in your editor
(``C-c C-d`` in Emacs, ``<LocalLeader>h`` in Vim).

Comments
========

Use comments to explain why code is written the way that it
is. Idris’s comment syntax is the same as that of Haskell: lines
beginning with ``--`` are comments, and regions bracketed by ``{-``
and ``-}`` are comments even if they extend across multiple
lines. These can be used to comment out lines of code or provide
simple documentation for the readers of Idris code.

Inline Documentation
====================

Idris also supports a comprehensive and rich inline syntax for Idris
code to be generated. This syntax also allows for named parameters and
variables within type signatures to be individually annotated using a
syntax similar to Javadoc parameter annotations.

Documentation always comes before the declaration being documented.
Inline documentation applies to either top-level declarations or to
constructors. Documentation for specific arguments to constructors, type
constructors, or functions can be associated with these arguments using
their names.

The inline documentation for a declaration is an unbroken string of
lines, each of which begins with ``|||`` (three pipe symbols). The
first paragraph of the documentation is taken to be an overview, and
in some contexts, only this overview will be shown. After the
documentation for the declaration as a whole, it is possible to
associate documentation with specific named parameters, which can
either be explicitly name or the results of converting free variables
to implicit parameters.  Annotations are the same as with Javadoc
annotations, that is for the named parameter ``(n : T)``, the
corresponding annotation is ``||| @ n Some description`` that is
placed before the declaration.

Documentation is written in Markdown, though not all contexts will
display all possible formatting (for example, images are not displayed
when viewing documentation in the REPL, and only some terminals render
italics correctly). A comprehensive set of examples is given below.

.. code-block:: idris


    ||| Modules can also be documented.
    module Docs

    ||| Add some numbers.
    |||
    ||| Addition is really great. This paragraph is not part of the overview.
    ||| Still the same paragraph. 
    |||
    ||| You can even provide examples which are inlined in the documentation:
    ||| ```idris example
    ||| add 4 5
    ||| ```
    ||| 
    ||| Lists are also nifty:
    ||| * Really nifty!
    ||| * Yep!
    ||| * The name `add` is a **bold** choice
    ||| @ n is the recursive param
    ||| @ m is not
    add : (n, m : Nat) -> Nat
    add Z     m = m
    add (S n) m = S (add n m)


    ||| Append some vectors
    ||| @ a the contents of the vectors
    ||| @ xs the first vector (recursive param)
    ||| @ ys the second vector (not analysed)
    appendV : (xs : Vect n a) -> (ys : Vect m a) -> Vect (add n m) a
    appendV []      ys = ys
    appendV (x::xs) ys = x :: appendV xs ys

    ||| Here's a simple datatype
    data Ty =
      ||| Unit
      UNIT |
      ||| Functions
      ARR Ty Ty

    ||| Points to a place in a typing context
    data Elem : Vect n Ty -> Ty -> Type where
      Here : {ts : Vect n Ty} -> Elem (t::ts) t
      There : {ts : Vect n Ty} -> Elem ts t -> Elem (t'::ts) t

    ||| A more interesting datatype
    ||| @ n the number of free variables
    ||| @ ctxt a typing context for the free variables
    ||| @ ty the type of the term
    data Term : (ctxt : Vect n Ty) -> (ty : Ty) -> Type where

      ||| The constructor of the unit type
      ||| More comment
      ||| @ ctxt the typing context
      UnitCon : {ctxt : Vect n Ty} -> Term ctxt UNIT

      ||| Function application
      ||| @ f the function to apply
      ||| @ x the argument
      App : {ctxt : Vect n Ty} -> (f : Term ctxt (ARR t1 t2)) -> (x : Term ctxt t1) -> Term ctxt t2

      ||| Lambda
      ||| @ body the function body
      Lam : {ctxt : Vect n Ty} -> (body : Term (t1::ctxt) t2) -> Term ctxt (ARR t1 t2)

      ||| Variables
      ||| @ i de Bruijn index
      Var : {ctxt : Vect n Ty} -> (i : Elem ctxt t) -> Term ctxt t

    ||| A computation that may someday finish
    codata Partial : Type -> Type where

      ||| A finished computation
      ||| @ value the result
      Now : (value : a) -> Partial a

      ||| A not-yet-finished computation
      ||| @ rest the remaining work
      Later : (rest : Partial a) -> Partial a

    ||| We can document records, including their fields and constructors
    record Yummy where
      ||| Make a yummy
      constructor MkYummy
      ||| What to eat
      food : String

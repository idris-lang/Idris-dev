*****************
Idris' Internals
*****************

Note: this is still a fairly raw set of notes taken by David
Christiansen at Edwin's presentation at the 2013 Idris Developers
Meeting. They're in the process of turning into a useful guide - feel
free to contribute.

This document assumes that you are already familiar with Idris. It is
intended for those who want to work on the internals.

People looking to develop new back ends may want to look at [[Idris back
end IRs\|Idris-back-end-IRs]]

Core/TT.hs
==========

Idris is compiled to a simple, explicit core language. This core
language is called TT because it looks a bit like a Π. It's a minimal
language, with a locally nameless representation. That is, local
variables are represented with de Bruijn indices and globally-defined
constants are represented with names.

The ``TT`` datatype uses a trick that is common in the Idris code: it is
polymorphic over the type of names stored in it, and it derives
``Functor``. This allows ``fmap`` to be used as a general-purpose
traversal.

There is a general construction for binders, used for λ, Π, and
let-bindings. These are distinguished using a ``BinderType``.

During compilation, some terms (especially types) will be erased. This
is represented using the ``Erased`` constructor of ``TT``. A handy trick
when generating TT terms is to insert ``Erased`` where a term is
uniquely determined, as the typechecker will fill it out.

The constructor ``Proj`` is a result of the optimizer. It is used to
extract a specific constructor argument, in a more economical way than
defining a new pattern-matching operation.

The datatype ``Raw`` represents terms that have not yet been
typechecked. The typechecker converts a ``Raw`` to a ``TT`` if it can.

Core/CaseTree.hs
================

Case trees are used to represent top-level pattern-matching definitions
in the TT language.

Just as with the ``TT`` datatype, the ``deriving Functor`` trick is used
with ``SC`` and ``CaseAlt`` to get GHC to generate a function for
mapping over contained terms.

Constructor cases (``ConCase`` in ``CaseAlt``) refer to numbered
constructors. Every constructor is numbered 0,1,2,…. At this stage in
the compiler, the tags are datatype-local. After defunctionalization,
however, they are made globally unique.

The ``n+1`` patterns (``SucCase``) and hacky-seeming things are to make
code fast -- please ask before "cleaning up" the representation.

Core/Evaluate.hs
================

This module contains the main evaluator for Idris. The evaluator is used
both at the REPL and during type checking, where normalised terms need
to be compared for equality.

A key datatype in the evaluator is a *context*. Contexts are mappings
from global names to their values, but they are organized to make
type-directed disambiguation quick. In particular, the main part of a
name that a user might type is used as the key, and its values are maps
from namespaces to actual values.

The datatype ``Def`` represents a definition in the global context. All
global names map to this structure.

``Type`` and ``Term`` are both synonyms for ``TT``.

Datatypes are represented by a ``TyDecl`` with the appropriate
``NameType``. A ``Function`` is a global constant term with an annotated
type, ``Operator`` represents primitives implemented in Haskell, and
``CaseOp`` represents ordinary pattern-matching definitions. ``CaseOp``
has four versions for different purposes, and all are saved because
that's easiest.

``CaseInfo``: the ``tc_dictionary`` is because it's a type class
dictionary which makes totality checking easier.

The ``normalise*`` functions give different behaviors - but
``normalise`` is the most common.

``normaliseC`` - "resolved" means with names converted to de Bruijn
indices as appropriate.

``normaliseAll`` - reduce everything, even if it's non-total

``normaliseTrace`` - special-purpose for debugging

``simplify`` - reduce the things that are small - the list argument is
the things to not reduce.

Core/Typecheck.hs
=================

Standard stuff. Hopefully no changes are necessary.

Core/Elaborate.hs
=================

Idris definitions are elaborated one by one and turned into the
corresponding TT. This is done with a tactic language as an EDSL in the
Elab monad (or Elab' when there's a custom state).

Lots of plumbing for errors.

All elaboration is relative to a global context.

The string in the pair returned by elaborate is log information.

See JFP paper, but the names don't necessarily map to each other. The
paper is the "idealized version" without logging, additional state, etc.

All the tactics take Raws, typechecking happens there.

claim (x : t) assumes a new x : t.

PLEASE TIDY THINGS UP!

proofSearch flag to try' is whether the failure came from a human (so
fail) or from a machine (so continue)

Idris-level syntax for providing alternatives explicitly: (\| x, y, z
\|) try x, y, z in order, and take the first that succeeds.

Core/ProofState.hs
==================

Core/Unify.hs
=============

Deals with unification. Unification can reply with: - this works - this
can never work - this will work if these other unification problems work
out (eg unifying f x with 1)

match\_unify: same thing as unification except it's just matching name
against name, term against term. x + y matches to 0 + y with x = 0. Used
for <== syntax as well as type class resolution.

Idris/AbsSyntaxTree.hs
======================

PTerm is the datatype of Idris syntax. P is for Program. Each PTerm
turns into a TT term by applying a series of tactics.

IState is the major interpreter state. The global context is the
tt\_ctxt field.

Ctxt maps possibly ambiguous names to their referents.

Idris/ElabDecls.hs
==================

This is where the actual elaboration from PTerm to TT happens.

Idris/ElabTerm.hs
=================

build is the function that creates a Raw. All the "junk" is to deal with
things like metavars and so forth. It has to remember what names are
still to be defined, and it doesn't yet know the type (filled in by
unificaiton later). Also case expressions have to turn into top-level
functions.

resolveTC is type class resolution.

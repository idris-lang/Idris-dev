*******************
Language Extensions
*******************



Type Providers
===============

Idris type providers are a way to get the type system to reflect
observations about the world outside of Idris. Similarly to `F# type
providers <http://msdn.microsoft.com/en-us/library/vstudio/hh156509.aspx>`__,
they cause effectful computations to run during type checking, returning
information that the type checker can use when checking the rest of the
program. While F# type providers are based on code generation, Idris
type providers use only the ordinary execution semantics of Idris to
generate the information.

A type provider is simply a term of type ``IO (Provider t)``, where
``Provider`` is a data type with constructors for a successful result
and an error. The type ``t`` can be either ``Type`` (the type of types)
or a concrete type. Then, a type provider ``p`` is invoked using the
syntax ``%provide (x : t) with p``. When the type checker encounters
this line, the IO action ``p`` is executed. Then, the resulting term is
extracted from the IO monad. If it is ``Provide y`` for some ``y : t``,
then ``x`` is bound to ``y`` for the remainder of typechecking and in
the compiled code. If execution fails, a generic error is reported and
type checking terminates. If the resulting term is ``Error e`` for some
string ``e``, then type checking fails and the error ``e`` is reported
to the user.

Example Idris type providers can be seen at `this
repository <https://github.com/david-christiansen/idris-type-providers>`__.
More detailed descriptions are available in David Christiansen's `WGP
'13 paper <http://dx.doi.org/10.1145/2502488.2502495>`__ and `M.Sc.
thesis <http://itu.dk/people/drc/david-christiansen-thesis.pdf>`__.

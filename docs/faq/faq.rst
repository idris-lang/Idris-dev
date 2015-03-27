==========================
Frequently Asked Questions
==========================

What are the differences between Agda and Idris?
------------------------------------------------

The main difference is that Idris has been designed from the start to support
verified systems programming through easy interoperability with C and high
level language constructs to support domain specific language implementation.
Idris emphasises general-purpose programming, rather than theorem proving, and
as such includes higher level programming constructs such as type classes and
do notation. Idris also supports tactic based theorem proving, and has a
lightweight Hugs/GHCI style interface.

Why does Idris use eager evaluation rather than lazy? 
-----------------------------------------------------

Idris uses eager evaluation for more predictable performance, in particular
because one of the longer term goals is to be able to write efficient and
verified low level code such as device drivers and network infrastructure.
Furthermore, the Idris type system allows us to state precisely the type
of each value, and therefore the run-time form of each value. In a lazy
language, consider a value of type ``Int``:

.. code-block:: idris

    thing : Int

What is the representation of ``thing`` at run-time? Is it a bit pattern
representing an integer, or is it a pointer to some code which will compute
an integer? In Idris, we have decided that we would like to make this
distinction precise, in the type:

.. code-block:: idris

    thing_val : Int
    thing_comp : Lazy Int

Here, it is clear from the type that ``thing_val`` is guaranteed to be a
concrete ``Int``, whereas ``thing_comp`` is a computation which will produce an
``Int``.

How can I make lazy control structures?
---------------------------------------

You can make control structures  using the special Lazy type. For example,
``if...then...else`` is defined as follows in the library:

.. code-block:: idris

    boolElim : Bool -> (t : Lazy a) -> (e : Lazy a) -> a
    boolElim True  t e = t
    boolElim False t e = e

    syntax if [test] then [t] else [e] = boolElim test t e

The type ``Lazy a`` for ``t`` and ``f`` indicates that those arguments will
only be evaluated if they are used, that is, they are evaluated lazily.

When will Idris be self-hosting?
--------------------------------

It’s not a priority, though not a bad idea in the long run. It would be a
worthwhile effort in the short term to implement libraries to support
self-hosting, such as a good parsing library.

Does Idris have Universe Polymorphism? What is the type of ``Type``?
--------------------------------------------------------------------

Rather than Universe polymorphism, Idris has a cumulative hierarchy of
universes; ``Type : Type 1``, ``Type 1 : Type 2``, etc. 
Cumulativity means that if ``x : Type n`` then also ``x : Type m``, 
provided that ``n <= m``.

What does the name ‘Idris’ mean?
--------------------------------

British people of a certain age may be familiar with this 
`singing dragon <https://www.youtube.com/watch?v=G5ZMNyscPcg>`_. If
that doesn’t help, maybe you can invent a suitable acronym :-) .

Where can I find more answers?
------------------------------

There is an `Unofficial FAQ
<https://github.com/idris-lang/Idris-dev/wiki/Unofficial-FAQ>`_ on the wiki on
github which answers more technical questions and may be updated more often.


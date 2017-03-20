************
Introduction
************

Pure functional languages with dependent types such as `Idris
<http://www.idris-lang.org/>`_ support reasoning about programs directly
in the type system, promising that we can *know* a program will run
correctly (i.e. according to the specification in its type) simply
because it compiles. Realistically, though, things are not so simple:
programs have to interact with the outside world, with user input,
input from a network, mutable state, and so on. 

In general, software relies on state, and many components rely on state machines. For
example, they describe network transport protocols like TCP, and
implement event-driven systems and regular expression matching. Furthermore,
many fundamental resources like network sockets and files are, implicitly,
managed by state machines, in that certain operations are only valid on
resources in certain states, and those operations can change the states of the
underlying resource. For example, it only makes sense to send a message on a
connected network socket, and closing a socket changes its state from "open" to
"closed". State machines can also encode important security properties. For
example, in the software which implements an ATM, it’s important that the ATM
dispenses cash only when the machine is in a state where a card has been
inserted and the PIN verified.

In this tutorial I will introduce the `Control.ST` library, which is included
with the Idris distribution and supports programming and reasoning with
state and side effects.
This tutorial assumes familiarity with pure programming in Idris,
as described in :ref:`tutorial-index`.

The `ST` library allows us to write programs which are composed of multiple
state transition systems. It supports composition in two ways: firstly, we can
use several independently implemented state transition systems at once;
secondly, we can implement one state transition system in terms of others.


********
Overview
********

Pure functional languages with dependent types such as `Idris
<http://www.idris-lang.org/>`_ support reasoning about programs directly
in the type system, promising that we can *know* a program will run
correctly (i.e. according to the specification in its type) simply
because it compiles. 

Realistically, though,  software relies on state, and many components rely on state machines. For
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

In this tutorial we will introduce the ``Control.ST`` library, which is included
with the Idris distribution (currently as part of the ``contrib`` package)
and supports programming and reasoning with state and side effects.  This
tutorial assumes familiarity with pure programming in Idris, as described in
:ref:`tutorial-index`.
For further background information, the ``ST`` library is based on ideas
discussed in Chapter 13 (available as a free sample chapter) and Chapter 14
of `Type-Driven Development with Idris <https://www.manning.com/books/type-driven-development-with-idris>`_.

The ``ST`` library allows us to write programs which are composed of multiple
state transition systems. It supports composition in two ways: firstly, we can
use several independently implemented state transition systems at once;
secondly, we can implement one state transition system in terms of others.


Introductory example: a data store requiring a login
====================================================

Many software components rely on some form of state, and there may be
operations which are only valid in specific states. For example, consider
a secure data store in which a user must log in before getting access to
some secret data. This system can be in one of two states:

* ``LoggedIn``, in which the user is allowed to read the secret
* ``LoggedOut``, in which the user has no access to the secret

We can provide commands to log in, log out, and read the data, as illustrated
in the following diagram:

|login|

The ``login`` command, if it succeeds, moves the overall system state from
``LoggedOut`` to ``LoggedIn``. The ``logout`` command moves the state from
``LoggedIn`` to ``LoggedOut``. Most importantly, the ``readSecret`` command
is only valid when the system is in the ``LoggedIn`` state.

We routinely use type checkers to ensure that variables and arguments are used
consistently. However, statically checking that operations are performed only
on resources in an appropriate state is not well supported by mainstream type
systems. In the data store example, for example, it's important to check that
the user is successfully logged in before using ``readSecret``. The
``ST`` library allows us to represent this kind of *protocol* in the type
system, and ensure at *compile-time* that the secret is only read when the
user is logged in.

Outline
=======

This tutorial starts (:ref:`introst`) by describing how to manipulate
individual states, introduce a data type ``STrans`` for describing stateful
functions, and ``ST`` which describes top level state transitions.
Next (:ref:`smstypes`) it describes how to represent state machines in
types, and how to define *interfaces* for describing stateful systems.
Then (:ref:`composing`) it describes how to compose systems of multiple
state machines. It explains how to implement systems which use several
state machines at once, and how to implement a high level stateful system
in terms of lower level systems.
Finally (:ref:`netexample`) we'll see a specific example of a stateful
API in practice, implementing the POSIX network sockets API.

The ``Control.ST`` library is also described in a draft paper by
`Edwin Brady <https://edwinb.wordpress.com/>`_, "State Machines All The Way
Down", available `here <https://www.idris-lang.org/drafts/sms.pdf>`_.
This paper presents many of the examples from this tutorial, and describes
the motivation, design and implementation of the library in more depth. 

.. |login| image:: ../image/login.png
                   :width: 500px



.. _sect-starting:

===============
Getting Started
===============

Prerequisites
-------------

Before installing Idris, you will need to make sure you have all
of the necessary libraries and tools. You will need:

- A fairly recent Haskell platform. Version 2013.2.0.0 should be
   sufficiently recent, though it is better to be completely up to
   date.

- The *GNU Multiple Precision Arithmetic Library* (GMP) is available
   from MacPorts/Homebrew and all major Linux distributions.

Downloading and Installing
--------------------------

The easiest way to install Idris, if you have all of the
prerequisites, is to type:

::

    cabal update; cabal install idris

This will install the latest version released on Hackage, along with
any dependencies. If, however, you would like the most up to date
development version you can find it, as well as build intructions, on
GitHub at: https://github.com/idris-lang/Idris-dev.

To check that installation has succeeded, and to write your first
Idris program, create a file called “``hello.idr``” containing the
following text:

If you are familiar with Haskell, it should be fairly clear what the
program is doing and how it works, but if not, we will explain the
details later. You can compile the program to an executable by
entering ``idris hello.idr -o hello`` at the shell prompt. This will
create an executable called ``hello``, which you can run:

::

    $ idris hello.idr -o hello
    $ ./hello
    Hello world

Note that the ``$`` indicates the shell prompt! Should the Idris
executable not be found please ensure that you have added
``~/.cabal/bin`` to your ``$PATH`` environment variable. Mac OS X
users may find they need to use ``~/Library/Haskell/bin``
instead. Some useful options to the Idris command are:

- ``-o prog`` to compile to an executable called ``prog``.

- ``--check`` type check the file and its dependencies without
   starting the interactive environment.

- ``--help`` display usage summary and command line options

The Interactive Environment
---------------------------

Entering ``idris`` at the shell prompt starts up the interactive
environment. You should see something like the following:

.. literalinclude:: ../listing/idris-prompt-start.txt

This gives a ``ghci`` style interface which allows evaluation of, as
well as type checking of, expressions; theorem proving, compilation;
editing; and various other operations. The command ``:?`` gives a list
of supported commands. Listing :ref:`run1` shows an example run in
which ``hello.idr`` is loaded, the type of ``main`` is checked and
then the program is compiled to the executable ``hello``. Type
checking a file, if successful, creates a bytecode version of the file
(in this case ``hello.ibc``) to speed up loading in future. The
bytecode is regenerated if the source file changes.

.. literalinclude:: ../listing/idris-prompt-helloworld.txt
   :caption: Sample Interactive Run
   :name: run1

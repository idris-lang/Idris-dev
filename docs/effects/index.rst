.. _eff-tutorial-index:

####################
The Effects Tutorial
####################

A tutorial on the `Effects` package in `Idris`.

.. topic:: Effects and the ``Control.ST`` module

   There is a new module in the ``contrib`` package, ``Control.ST``, which
   provides the resource tracking facilities of `Effects` but with
   better support for creating and deleting resources, and implementing
   resources in terms of other resources.

   Unless you have a particular reason to use `Effects` you are strongly
   recommended to use ``Control.ST`` instead. There is a tutorial available
   on this site for ``Control.ST`` with several examples
   (:ref:`st-tutorial-index`).

.. note::

   The documentation for Idris has been published under the Creative
   Commons CC0 License. As such to the extent possible under law, *The
   Idris Community* has waived all copyright and related or neighbouring
   rights to Documentation for Idris.

   More information concerning the CC0 can be found online at: http://creativecommons.org/publicdomain/zero/1.0/

.. toctree::
   :maxdepth: 1

   introduction
   state
   simpleeff
   depeff
   impleff
   hangman
   conclusions
   summary

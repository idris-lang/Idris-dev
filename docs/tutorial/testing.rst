.. _tut-sect-testing:

**********************
Testing Idris Packages
**********************

The integrated build system includes a simple testing framework.
This framework collects functions listed in the ``ipkg`` file under ``tests``.
All test functions must return ``IO ()``.


When you enter ``idris --testpkg yourmodule.ipkg``,
the build system creates a temporary file in a fresh environment on your machine
by listing the ``tests`` functions under a single ``main`` function.
It compiles this temporary file to an executable and then executes it.


The tests themselves are responsible for reporting their success or failure.
Test functions commonly use ``putStrLn`` to report test results.
The test framework does not impose any standards for reporting and consequently
does not aggregate test results.


For example, lets take the following list of functions that are defined in a module called ``NumOps`` for a sample package ``maths``.

.. code-block:: idris
   :caption: Math/NumOps.idr

    module Maths.NumOps

    double : Num a => a -> a
    double a = a + a

    triple : Num a => a -> a
    triple a = a + double a

A simple test module, with a qualified name of ``Test.NumOps`` can be declared as

.. code-block:: idris
   :caption: Math/TestOps.idr

    module Test.NumOps

    import Maths.NumOps

    assertEq : Eq a => (given : a) -> (expected : a) -> IO ()
    assertEq g e = if g == e
        then putStrLn "Test Passed"
        else putStrLn "Test Failed"

    assertNotEq : Eq a => (given : a) -> (expected : a) -> IO ()
    assertNotEq g e = if not (g == e)
        then putStrLn "Test Passed"
        else putStrLn "Test Failed"

    testDouble : IO ()
    testDouble = assertEq (double 2) 4

    testTriple : IO ()
    testTriple = assertNotEq (triple 2) 5


The functions ``assertEq`` and ``assertNotEq`` are used to run expected passing, and failing, equality tests.
The actual tests are ``testDouble`` and ``testTriple``, and are declared in the ``maths.ipkg`` file as follows::

    package maths

    modules = Maths.NumOps
            , Test.NumOps

    tests = Test.NumOps.testDouble
          , Test.NumOps.testTriple


The testing framework can then be invoked using ``idris --testpkg maths.ipkg``::

    > idris --testpkg maths.ipkg
    Type checking ./Maths/NumOps.idr
    Type checking ./Test/NumOps.idr
    Type checking /var/folders/63/np5g0d5j54x1s0z12rf41wxm0000gp/T/idristests144128232716531729.idr
    Test Passed
    Test Passed

Note how both tests have reported success by printing a single ``.``
as we arranged for with the ``assertEq`` and ``assertNoEq`` functions.

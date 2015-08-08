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

    module Maths.NumOps

    double : Num a => a -> a
    double a = a + a

    triple : Num a => a -> a
    triple a = a + double a

A simple test module, with a qualified name of ``Test.NumOps`` can be declared as

.. code-block:: idris

    module Test.NumOps

    import Maths.NumOps

    assertEq : Eq a => (given : a) -> (expected : a) -> IO ()
    assertEq g e = if g == e
        then putStrLn "Test Passed"
        else putStrLn "Test failed"

    assertNotEq : Eq a => (given : a) -> (expected : a) -> IO ()
    assertNotEq g e = if not (g == e)
        then putStrLn "Test Passed"
        else putStrLn "Test failed"

    testDouble : IO ()
    testDouble = assertEq (double 2) 4

    testTriple : IO ()
    testTriple = assertNotEq (triple 2) 5


The functions ``assertEq`` and ``assertNotEq`` are used to run expected passing, and failing, equality tests.
The actual tests are ``testDouble`` and ``testTriple``, and are declared in the ``maths.ipkg`` file as follows::

    module maths

    module = Maths.NumOps
           , Test.NumOps

    tests = Test.NumOps.testDouble
          , Test.NumOps.testTriple


The testing framework can be invoked using: ``idris --testpkg maths.ipkg``.

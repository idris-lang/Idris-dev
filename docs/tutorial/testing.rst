.. _tut-sect-testing:

**********************
Testing Idris Packages
**********************

As part of the integrated build system a simple testing framework is provided.
This framework will collect a list of named functions and construct an Idris executable in a fresh environment on your machine.
This executable lists the named functions under a single ``main`` function, and imports the complete list of modules for the package.


It is up to the developer to ensure the correct reporting of test results, and the structure and nature of how the tests are run.
Further, all test functions must return ``IO ()``, and must be listed in the ``ipkg`` file under ``tests``, and rhe modules containing the test functions must also be listed in the modules section of the ``iPKG`` file.


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

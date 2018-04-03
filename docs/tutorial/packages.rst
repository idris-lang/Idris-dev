.. _sect-packages:

********
Packages
********

Idris includes a simple build system for building packages and executables
from a named package description file. These files can be used with the
Idris compiler to manage the development process .

Package Descriptions
====================

A package description includes the following:

+ A header, consisting of the keyword ``package`` followed by a package
  name. Package names can be any valid Idris identifier. The iPKG
  format also takes a quoted version that accepts any valid filename.

+ Fields describing package contents, ``<field> = <value>``.

At least one field must be the modules field, where the value is a
comma separated list of modules. For example, given an idris package
``maths`` that has modules ``Maths.idr``, ``Maths.NumOps.idr``,
``Maths.BinOps.idr``, and ``Maths.HexOps.idr``, the corresponding
package file would be:

::

    package maths

    modules = Maths
            , Maths.NumOps
            , Maths.BinOps
            , Maths.HexOps


Other examples of package files can be found in the ``libs`` directory
of the main Idris repository, and in `third-party libraries
<https://github.com/idris-lang/Idris-dev/wiki/Libraries>`_.


Using Package files
===================

Idris itself is aware about packages, and special commands are
available to help with, for example, building packages, installing
packages, and cleaning packages.  For instance, given the ``maths``
package from earlier we can use Idris as follows:

+ ``idris --build maths.ipkg`` will build all modules in the package

+ ``idris --install maths.ipkg`` will install the package, making it
  accessible by other Idris libraries and programs.

+ ``idris --clean maths.ipkg`` will delete all intermediate code and
  executable files generated when building.

Once the maths package has been installed, the command line option
``--package maths`` makes it accessible (abbreviated to ``-p maths``).
For example:

::

    idris -p maths Main.idr


Testing Idris Packages
======================

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

For example, lets take the following list of functions that are defined in a
module called ``NumOps`` for a sample package ``maths``:

.. name: Math/NumOps.idr
.. code-block:: idris

    module Maths.NumOps

    %access export -- to make functions under test visible

    double : Num a => a -> a
    double a = a + a

    triple : Num a => a -> a
    triple a = a + double a


A simple test module, with a qualified name of ``Test.NumOps`` can be declared as:

.. name: Math/TestOps.idr
.. code-block:: idris

    module Test.NumOps

    import Maths.NumOps

    %access export  -- to make the test functions visible

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


The functions ``assertEq`` and ``assertNotEq`` are used to run expected passing,
and failing, equality tests. The actual tests are ``testDouble`` and ``testTriple``,
and are declared in the ``maths.ipkg`` file as follows:

::

    package maths

    modules = Maths.NumOps
            , Test.NumOps

    tests = Test.NumOps.testDouble
          , Test.NumOps.testTriple


The testing framework can then be invoked using ``idris --testpkg maths.ipkg``:

::

    > idris --testpkg maths.ipkg
    Type checking ./Maths/NumOps.idr
    Type checking ./Test/NumOps.idr
    Type checking /var/folders/63/np5g0d5j54x1s0z12rf41wxm0000gp/T/idristests144128232716531729.idr
    Test Passed
    Test Passed

Note how both tests have reported success by printing ``Test Passed``
as we arranged for with the ``assertEq`` and ``assertNoEq`` functions.

Package Dependencies Using Atom
===============================

If you are using the Atom editor and have a dependency on another package,
corresponding to for instance ``import Lightyear`` or ``import Pruviloj``,
you need to let Atom know that it should be loaded. The easiest way to
accomplish that is with a .ipkg file. The general contents of an ipkg file
will be described in the next section of the tutorial, but for now here is
a simple recipe for this trivial case:

- Create a folder myProject.

- Add a file myProject.ipkg containing just a couple of lines:

.. code-block:: idris

    package myProject

    pkgs = pruviloj, lightyear

- In Atom, use the File menu to Open Folder myProject.

More information
================

More details, including a complete listing of available fields, can be
found in the reference manual in :ref:`ref-sect-packages`.

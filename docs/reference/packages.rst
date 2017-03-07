.. _ref-sect-packages:

********
Packages
********

Idris includes a simple system for building packages from a
package description file. These files can be used with the Idris
compiler to manage the development process of your Idris
programmes and packages.

Package Descriptions
====================

A package description includes the following:

+ A header, consisting of the keyword package followed by the package
  name. Package names can be any valid Idris identifier. The iPKG
  format also takes a quoted version that accepts any valid filename.
+ Fields describing package contents, ``<field> = <value>``

At least one field must be the modules field, where the value is a
comma separated list of modules.  For example, a library test which
has two modules ``foo.idr`` and ``bar.idr`` as source files would be
written as follows::

    package foo

    modules = foo, bar

Other examples of package files can be found in the ``libs`` directory
of the main Idris repository, and in `third-party libraries <https://github.com/idris-lang/Idris-dev/wiki/Libraries>`_.

Metadata
--------

From Idris `v0.12` the `iPKG` format supports additional metadata
associated with the package.
The added fields are:

+ ``brief = "<text>"``, a string literal containing a brief description
  of the package.

+ ``version = <text>``, a version string to associate with the package.

+ ``readme = <file>``, location of the README file.

+ ``license = <text>``, a string description of the licensing
  information.

+ ``author = <text>``, the author information.

+ ``maintainer = <text>``, Maintainer information.

+ ``homepage = <url>``, the website associated with the package.

+ ``sourceloc = <url>``, the location of the DVCS where the source
  can be found.

+ ``bugtracker = <url>``, the location of the project's bug tracker.


Common Fields
-------------

Other common fields which may be present in an ``ipkg`` file are:

+ ``sourcedir = <dir>``, which takes the directory (relative to the
  current directory) which contains the source. Default is the current
  directory.

+ ``executable = <output>``, which takes the name of the executable
  file to generate. Executable names can be any valid Idris
  identifier. the iPKG format also takes a quoted version that accepts
  any valid filename.

+ ``main = <module>``, which takes the name of the main module, and
  must be present if the executable field is present.

+ ``opts = "<idris options>"``, which allows options to be passed to
  Idris.

+ ``pkgs = <pkg name> (',' <pkg name>)+``, a comma separated list of
  package names that the Idris package requires.

Binding to C
------------

In more advanced cases, particularly to support creating bindings to
external ``C`` libraries, the following options are available:

+ ``makefile = <file>``, which specifies a ``Makefile``, to be built
  before the Idris modules, for example to support linking with a
  ``C`` library.

+ ``libs = <libs>``, which takes a comma separated list of libraries
  which must be present for the package to be usable.

+ ``objs = <objs>``, which takes a comma separated list of additional
  files to be installed (object files, headers), perhaps generated
  by the ``Makefile``.

Testing
--------

For testing Idris packages there is a rudimentary testing harness, run in the ``IO`` context.
The ``iPKG`` file is used to specify the functions used for testing.
The following option is available:

+ ``tests = <test functions>``, which takes the qualified names of all test functions to be run.

.. IMPORTANT::
  The modules containing the test functions must also be added to the list of modules.

Comments
---------

Package files support comments using the standard Idris singleline ``--`` and multiline ``{- -}`` format.

Using Package files
===================

Given an Idris package file ``text.ipkg`` it can be used with the Idris compiler as follows:

+ ``idris --build test.ipkg`` will build all modules in the package

+ ``idris --install test.ipkg`` will install the package, making it
  accessible by other Idris libraries and programs.

+ ``idris --clean test.ipkg`` will delete all intermediate code and
  executable files generated when building.

+ ``idris --mkdoc test.ipkg`` will build HTML documentation for your package in the folder ``test_doc`` in your project's root directory.

+ ``idris --installdoc test.ipkg`` will install the packages documentation into Idris' central documentation folder located at ``idris --docdir``.

+ ``idris --checkpkg test.ipkg`` will type check all modules in the package only. This differs from build that type checks **and** generates code.

+ ``idris --testpkg test.ipkg`` will compile and run any embedded tests you have specified in the ``tests`` parameter.

When building or install packages the commandline flag ``--warnipkg`` will audit the project and warn of any potentiable problems.

Once the test package has been installed, the command line option
``--package test`` makes it accessible (abbreviated to ``-p test``).
For example::

    idris -p test Main.idr

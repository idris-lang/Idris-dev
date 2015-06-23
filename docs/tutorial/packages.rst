********
Packages
********


Idris includes a simple build system for building packages and executables from a named package description file.
These files can be used with the Idris compiler to manage the development process .

Package Descriptions
====================

A package description includes the following:

+ A header, consisting of the keyword package followed by the package name.
+ Fields describing package contents, ``<field> = <value>``

At least one field must be the modules field, where the value is a
comma separated list of modules.  For example, given an idris package
``maths`` that has modules ``Maths.idr``, ``Maths.NumOps.idr``,
``Maths.BinOps.idr``, and ``Maths.HexOps.idr``, the corresponding
package file would be::

    package maths

    modules = Maths
            , Maths.NumOps
            , Maths.BinOps
            , Maths.HexOps


Other examples of package files can be found in the ``libs`` directory
of the main Idris repository, and in `third-party libraries <https://github.com/idris-lang/Idris-dev/wiki/Libraries>`_.
More details including a complete listing of available fields can be found in :ref:`ref-sect-packages`.


Using Package files
===================

Given an Idris package file ``maths.ipkg`` it can be used with the Idris compiler as follows:

+ ``idris --build maths.ipkg`` will build all modules in the package

+ ``idris --install maths.ipkg`` will install the package, making it
  accessible by other Idris libraries and programs.

+ ``idris --clean maths.ipkg`` will delete all intermediate code and
  executable files generated when building.

+ ``idris --mkdoc maths.ipkg`` will build HTML documentation for your
  package in the folder ``maths_doc`` in your project's root
  directory.

+ ``idris --checkpkg maths.ipkg`` will type check all modules in the
  package only. This differs from build that type checks **and**
  generates code.

+ ``idris --mathspkg maths.ipkg`` will compile and run any embedded
  mathss you have specified in the ``tests`` paramater. More
  information about mathsing is given in the next section.

Once the maths package has been installed, the command line option
``--package maths`` makes it accessible (abbreviated to ``-p maths``).
For example::

    idris -p maths Main.idr

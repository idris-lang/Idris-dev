***********************
Compilation and Logging
***********************

This section provides information about the Idris compilation process, and
provides details over how you can follow the process through logging.

Compilation Process
===================

Idris follows the following compilation process:

#. Parsing
#. Type Checking

   #. Elaboration
   #. Coverage
   #. Unification
   #. Totality Checking
   #. Erasure

#. Code Generation

   #. Defunctionalisation
   #. Inlining
   #. Resolving variables
   #. Code Generation


Type Checking Only
==================

With Idris you can ask it to terminate the compilation process after type checking has completed. This is achieved through use of either:

+ The command line options

  + ``--check`` for files
  + ``--checkpkg`` for packages

+ The REPL command: ``:check``

Use of this option will still result in the generation of the Idris binary ``.ibc`` files, and is suitable if you do not wish to generate code from one of the supported backends.

Logging Output
==============

The internal operation of Idris is captured using a category based logger.
Currently, the logging infrastructure has support for the following categories:

+ Parser
+ Elaborator
+ Code generation
+ Erasure
+ Coverage Checking
+ IBC generation


These categories are specified using the command-line option:
``--logging-categories CATS``, where ``CATS`` is a quoted colon
seperated string of the categories you want to see. By default if this
option is not specified all categories are allowed.  Sub-categories
have yet to be defined but will be in the future, especially for the
elaborator.

Further, the verbosity of logging can be controlled by specifying a
logging level between: 1 to 10 using the command-line option: ``--log
<level>``.

+ Level 0: Show no logging output. Default level
+ Level 1: High level details of the compilation process.
+ Level 2: Provides details of the coverage checking, and further details the elaboration process specifically: Interface, Clauses, Data, Term, and Types,
+ Level 3: Provides details of compilation of the IRTS, erasure, parsing, case splitting, and further details elaboration of: Instances, Providers, and Values.
+ Level 4: Provides further details on: Erasure, Coverage Checking, Case splitting, and elaboration of clauses.
+ Level 5: Provides details on the prover, and further details elaboration (adding declarations) and compilation of the IRTS.
+ Level 6: Further details elaboration and coverage checking.
+ Level 7:
+ Level 8:
+ Level 9:
+ Level 10: Further details elaboration.

Environment Variables
=====================

Several paths set by default within the Idris compiler can be
overridden through environment variables.  The provided variables are:

* `IDRIS_CC` Change the `C` compiler used by the `C` backend.
* `IDRIS_CFLAGS` Change the `C` flags passed to the `C` compiler.
* `TARGET`   Change the target directory to generate files.
* `IDRIS_LIBRARY_PATH` Change the location of where installed packages are found.

Alternativly, and perhaps a cleaner approach is to configure these
options using the CLI options.  Idris also supports options to augment
the paths used, and pass options to the code generator backend.

The option `--cg-opt <ARG>` can be used to pass options to the code
generator. The format of `<ARG>` is dependent on the selected backend.

Further, Idris does support multiple include paths.  The CLI option
`-i <dir>` allows you to add a directory to the library search path; this
option can be used multiple times. This is a cleaner option when you
wish to add single directories to the `IDRIS_LIBRARY_PATH` than
ammending `IDRIS_LIBRARY_PATH` directly.
To add directories to the source search path, use the `--sourcepath <dir>` option.

Moreover, rather than using `TARGET` the CLI option `--ibcsubdir` can
be used to direct where built IBC files are placed.

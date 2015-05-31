***********************
Compilation and Logging
***********************


This section provides highlights of the Idris compilation process, and
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

Logging of the Idris output can be used to diagnose problems with the compilation of your program.
Idris supports the logging at various different levels of verbosity: 1 to 10.

+ Level 0: Show no logging output. Default level
+ Level 1: High level details of the compilation process.
+ Level 2: Provides details of the coverage checking, and further details the elaboration process specifically: Class, Clauses, Data, Term, and Types,
+ Level 3: Provides details of compilation of the IRTS, erasue, parsing, case splitting, and further details elaboration of: Instances, Providers, and Values.
+ Level 4: Provides further details on: Erasure, Coverage Checking, Case splitting, and elaboration of clauses.
+ Level 5: Provides details on the prover, and further details elaboration (adding declarations) and compilation of the IRTS.
+ Level 6: Further details elaboration and coverage checking.
+ Level 7:
+ Level 8:
+ Level 9:
+ Level 10: Further details elaboration.

************************
Code Generation Targets
************************

``Idris`` has been designed such that the compiler can generate code for
different backends upon request. By default ``Idris`` generates a ``C``
backend when generating an executable. Included within the standard Idris installation are backends for Javascript and Node.js.

However, there are third-party code generators out there.  Below we
describe some of these backends and how you can use them when
compiling your ``Idris`` code. If you want to write your own codegen for your language there is a `stub project on GitHub <https://github.com/idris-lang/idris-emptycg>`__ that can help point you in the right direction.

Official Backends
==================

C Language
----------

Javascript
----------

To generate code that is tailored for running in the browser
issue the following command:

::

    $ idris --codegen javascript hello.idr -o hello.js


Generating code for NodeJS is slightly different. Idris outputs a
JavaScript file that can be directly executed via node.

::

    $ idris --codegen node hello.idr -o hello
    $ ./hello
    Hello world


Idris can produce very big chunks of JavaScript code (hello world
weighs in at 1500 lines). However, the generated code can be minified
using the `closure-compiler
<https://developers.google.com/closure/compiler/>`__ from Google.

::

   java -jar compiler.jar --compilation_level ADVANCED_OPTIMIZATIONS --js hello.js


Node.js
-------


Third Party
============

.. note::

   These are third-party code generations and may have bit-rotted or
   do not work with current versions of Idris. Please speak to the
   project's maintainors if there are any problems.


CIL (.NET, Mono, Unity)
-----------------------

::

    idris --codegen cil Main.idr -o HelloWorld.exe \
      && mono HelloWorld.exe

The resulting assemblies can also be used with .NET or Unity.

Requires `idris-cil <https://github.com/bamboo/idris-cil>`__.

Erlang
------

`Available online <https://github.com/lenary/idris-erlang>`__

Java
----

`Available online <https://github.com/idris-hackers/idris-java>`__


::

   idris hello.idr --codegen java -o hello.jar


Note: The resulting .jar is automatically prefixed by a header including
an .sh script to allow executing it directly.

JVM
---

`Available online <https://github.com/mmhelloworld/idris-jvm>`__

LLVM
-----

`Available online <https://github.com/idris-hackers/idris-llvm>`__

Malfunction
------------

`Available online <https://github.com/stedolan/idris-malfunction>`__

Ocaml
-----

`Available online <https://github.com/ziman/idris-ocaml>`__

PHP
---

`Available online <https://github.com/edwinb/idris-php>`__

Python
------

`Available online <https://github.com/ziman/idris-py>`__

Ruby
----

`Available online <https://github.com/mrb/idris-ruby>`__

WS
---

`Available online <https://github.com/edwinb/WS-idr>`__

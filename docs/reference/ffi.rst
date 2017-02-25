******************************
New Foreign Function Interface
******************************

.. sectionauthor:: Edwin Brady

Ever since Idris has had multiple backends compiling to different
target languages on potentially different platforms, we have had the
problem that the foreign function interface (FFI) was written under
the assumption of compiling to C. As a result, it has been hard to
write generic code for multiple targets, or even to be sure that if
code compiles that it will run on the expected target.

As of 0.9.17, Idris will have a new foreign function interface (FFI)
which is aware of multiple targets. Users who are working with the
default code generator can happily continue writing programs as before
with no changes, but if you are writing bindings for an external
library, writing a back end, or working with a non-C back end, there
are some things you will need to be aware of, which this page
describes.

The ``IO'`` monad, and ``main``
===============================

The ``IO`` monad exists as before, but is now specific to the C
backend (or, more precisely, any backend whose foreign function calls
are compatible with C.) Additionally, there is now an ``IO'`` monad,
which is parameterised over a FFI descriptor:

.. code-block:: idris

    data IO' : (lang : FFI) -> Type -> Type

The Prelude defines two FFI descriptors which are imported
automatically, for C and JavaScript/Node, and defines ``IO`` to use
the C FFI and ``JS_IO`` to use the JavaScript FFI:

.. code-block:: idris

    FFI_C  : FFI
    FFI_JS : FFI

    IO : Type -> Type
    IO a = IO' FFI_C a

    JS_IO : Type -> Type
    JS_IO a = IO' FFI_JS a

As before, the entry point to an Idris program is ``main``, but the
type of ``main`` can now be any implementation of ``IO'``, e.g. the
following are both valid:

.. code-block:: idris

    main : IO ()
    main : JS_IO ()

The FFI descriptor includes details about which types can be
marshalled between the foreign language and Idris, and the "target" of
a foreign function call (typically just a String representation of the
function's name, but potentially something more complicated such as an
external library file or even a URL).

FFI descriptors
===============

An FFI descriptor is a record containing a predicate which holds when
a type can be marshalled, and the type of the target of a foreign
call:

.. code-block:: idris

    record FFI where
         constructor MkFFI
         ffi_types : Type -> Type
         ffi_fn : Type

For C, this is:

.. code-block:: idris

    ||| Supported C integer types
    public export
    data C_IntTypes : Type -> Type where
        C_IntChar   : C_IntTypes Char
        C_IntNative : C_IntTypes Int
        C_IntBits8  : C_IntTypes Bits8
        C_IntBits16 : C_IntTypes Bits16
        C_IntBits32 : C_IntTypes Bits32
        C_IntBits64 : C_IntTypes Bits64

    ||| Supported C function types
    public export
    data C_FnTypes : Type -> Type where
        C_Fn : C_Types s -> C_FnTypes t -> C_FnTypes (s -> t)
        C_FnIO : C_Types t -> C_FnTypes (IO' FFI_C t)
        C_FnBase : C_Types t -> C_FnTypes t

    ||| Supported C foreign types
    public export
    data C_Types : Type -> Type where
        C_Str   : C_Types String
        C_Float : C_Types Double
        C_Ptr   : C_Types Ptr
        C_MPtr  : C_Types ManagedPtr
        C_Unit  : C_Types ()
        C_Any   : C_Types (Raw a)
        C_FnT   : C_FnTypes t -> C_Types (CFnPtr t)
        C_IntT  : C_IntTypes i -> C_Types i

    ||| A descriptor for the C FFI. See the constructors of `C_Types`
    ||| and `C_IntTypes` for the concrete types that are available.
    %error_reverse
    public export
    FFI_C : FFI
        FFI_C = MkFFI C_Types String String

Foreign calls
=============

To call a foreign function, the ``foreign`` function is used. For
example:

.. code-block:: idris

    do_fopen : String -> String -> IO Ptr
    do_fopen f m
       = foreign FFI_C "fileOpen" (String -> String -> IO Ptr) f m

The ``foreign`` function takes an FFI description, a function name (the
type is given by the ``ffi_fn`` field of ``FFI_C`` here), and a function
type, which gives the expected types of the remaining arguments. Here,
we're calling an external function ``fileOpen`` which takes, in the C, a
``char*`` file name, a ``char*`` mode, and returns a file pointer. It is
the job of the C back end to convert Idris ``String`` to C ``char*``
and vice versa.

The argument types and return type given here must be present in the
``fn_types`` predicate of the ``FFI_C`` description for the foreign
call to be valid.

**Note** The arguments to ``foreign`` *must* be known at compile time,
because the foreign calls are generated statically. The ``%inline``
directive on a function can be used to give hints to help this, for
example a shorthand for calling external JavaScript functions:

.. code-block:: idris

    %inline
    jscall : (fname : String) -> (ty : Type) ->
              {auto fty : FTy FFI_JS [] ty} -> ty
    jscall fname ty = foreign FFI_JS fname ty

C callbacks
-----------
It is possible to pass an Idris function to a C function taking a function
pointer by using ``CFnPtr`` in the function type. The Idris function is passed
to ``MkCFnPtr`` in the arguments. The example below shows declaring the C standard
library function ``qsort`` which takes a pointer to a comparison function.

.. code-block:: idris

    myComparer : Ptr -> Ptr -> Int
    myComparer = ...

    qsort : Ptr -> Int -> Int -> IO ()
    qsort data elems elsize = foreign FFI_C "qsort"
                    (Ptr -> Int -> Int -> CFnPtr (Ptr -> Ptr -> Int) -> IO ())
                    data elems elsize (MkCFnPtr myComparer)

There are a few limitations to callbacks in the C FFI. The foreign function can't
take the function to make a callback of as an argument. This will give a
compilation error:

.. code-block:: idris

    -- This does not work
    example : (Int -> ()) -> IO ()
    example f = foreign FFI_C "callbacker" (CFnPtr (Int -> ()) -> IO ()) f

The other big limitation is that it doesn't support IO functions. Use
``unsafePerformIO`` to wrap them (i.e. to make an IO function usable as a callback, change the return type
from IOr to r, and change the = do to = unsafePerformIO $ do).

There are two special function names:
``%wrapper`` returns the function pointer that wraps an Idris function. This
is useful if the function pointer isn't taken by a C function directly but
should be inserted into a data structure. A foreign declaration using
``%wrapper`` must return ``IO Ptr``.

.. code-block:: idris

    -- this returns the C function pointer to a qsort comparer
    example_wrapper : IO Ptr
    example_wrapper = foreign FFI_C "%wrapper" (CFnPtr (Ptr -> Ptr -> Int) -> IO Ptr)
                            (MkCFnPtr myComparer)

``%dynamic`` calls a C function pointer with some arguments. This is useful if
a C function returns or data structure contains a C function pointer, for example
structs of function pointers are common in object-oriented C such as in COM or the
Linux kernel. The function type contains an extra ``Ptr`` at the start for the
function pointer. ``%dynamic`` can be seen as a pseudo-function that calls the
function in the first argument, passing the remaining arguments to it.

.. code-block:: idris

    -- we have a pointer to a function with the signature int f(int), call it
    example_dynamic : Ptr -> Int -> IO Int
    example_dynamic fn x = foreign FFI_C "%dynamic" (Ptr -> Int -> IO Int) fn x

If the foreign name is prefixed by a ``&``, it is treated as a pointer to the
global variable with the following name. The type must be just ``IO Ptr``.

.. code-block:: idris

    -- access the global variable errno
    errno : IO Ptr
    errno = foreign FFI_C "&errno" (IO Ptr)

For more complicated interactions with C (such as reading and setting fields of a C struct), there is
a module CFFI available in the contrib package.

FFI implementation
------------------

In order to write bindings to external libraries, the details of how
``foreign`` works are unnecessary --- you simply need to know that
``foreign`` takes an FFI descriptor, the function name, and its
type. It is instructive to look a little deeper, however:

The type of ``foreign`` is as follows:

.. code-block:: idris

    foreign : (ffi : FFI)
           -> (fname : ffi_fn f)
           -> (ty : Type)
           -> {auto fty : FTy ffi [] ty}
           -> ty

The important argument here is the implicit ``fty``, which contains a
proof (``FTy``) that the given type is valid according to the FFI
description ``ffi``:

.. code-block:: idris

    data FTy : FFI -> List Type -> Type -> Type where
         FRet : ffi_types f t -> FTy f xs (IO' f t)
         FFun : ffi_types f s -> FTy f (s :: xs) t -> FTy f xs (s -> t)

Notice that this uses the ``ffi_types`` field of the FFI descriptor
--- these arguments to ``FRet`` and ``FFun`` give explicit proofs that
the type is valid in this FFI. For example, the above ``do_fopen``
builds the following implicit proof as the ``fty`` argument to
``foreign``:

.. code-block:: idris

    FFun C_Str (FFun C_Str (FRet C_Ptr))

Compiling foreign calls
=======================

(This section assumes some knowledge of the Idris internals.)

When writing a back end, we now need to know how to compile
``foreign``.  We'll skip the details here of how a ``foreign`` call
reaches the intermediate representation (the IR), though you can look
in ``IO.idr`` in the ``prelude`` package to see a bit more detail ---
a ``foreign`` call is implemented by the primitive function
``mkForeignPrim``. The important part of the IR as defined in
``Lang.hs`` is the following constructor:

.. code-block:: idris

    data LExp = ...
              | LForeign FDesc -- Function descriptor
                         FDesc -- Return type descriptor
                         [(FDesc, LExp)]

So, a ``foreign`` call appears in the IR as the ``LForeign``
constructor, which takes a function descriptor (of a type given by the
``ffi_fn`` field in the FFI descriptor), a return type descriptor
(given by an application of ``FTy``), and a list of arguments with
type descriptors (also given by an application of ``FTy``).

An ``FDesc`` describes an application of a name to some arguments, and
is really just a simplified subset of an ``LExp``:

.. code-block:: idris

    data FDesc = FCon Name
               | FStr String
               | FUnknown
               | FApp Name [FDesc]

There are corresponding structures in the lower level IRs, such as the
defunctionalised, simplified and bytecode forms.

Our ``do_fopen`` example above arrives in the ``LExp`` form as:

.. code-block:: idris

    LForeign (FStr "fileOpen") (FCon (sUN "C_Ptr"))
             [(FCon (sUN "C_Str"), f), (FCon (sUN "C_Str"), m)]

(Assuming that ``f`` and ``m`` stand for the ``LExp`` representations
of the arguments.) This information should be enough for any back end
to marshal the arguments and return value appropriately.

.. note::

   When processing ``FDesc``, be aware that there may be implicit
   arguments, which have not been erased. For example, ``C_IntT`` has
   an implicit argument ``i``, so will appear in an ``FDesc`` as
   something of the form ``FApp (sUN "C_IntT") [i, t]`` where ``i`` is
   the implicit argument (which can be ignored) and ``t`` is the
   descriptor of the integer type. See ``CodegenC.hs``, specifically
   the function ``toFType``, to see how this works in practice.

JavaScript FFI descriptor
=========================

The JavaScript FFI descriptor is a little more complex, because the
JavaScript FFI supports marshalling functions. It is defined as
follows:

.. code-block:: idris

    mutual
      data JsFn t = MkJsFn t

      data JS_IntTypes  : Type -> Type where
           JS_IntChar   : JS_IntTypes Char
           JS_IntNative : JS_IntTypes Int

      data JS_FnTypes : Type -> Type where
           JS_Fn     : JS_Types s -> JS_FnTypes t -> JS_FnTypes (s -> t)
           JS_FnIO   : JS_Types t -> JS_FnTypes (IO' l t)
           JS_FnBase : JS_Types t -> JS_FnTypes t

      data JS_Types : Type -> Type where
           JS_Str   : JS_Types String
           JS_Float : JS_Types Double
           JS_Ptr   : JS_Types Ptr
           JS_Unit  : JS_Types ()
           JS_FnT   : JS_FnTypes a -> JS_Types (JsFn a)
           JS_IntT  : JS_IntTypes i -> JS_Types i

The reason for wrapping function types in a ``JsFn`` is to help the
proof search when building ``FTy``. We hope to improve proof search
eventually, but for the moment it works much more reliably if the
indices are disjoint! An example of using this appears in `IdrisScript
<https://github.com/idris-hackers/IdrisScript>`__ when setting
timeouts:

.. code-block:: idris

    setTimeout : (() -> JS_IO ()) -> (millis : Int) -> JS_IO Timeout
    setTimeout f millis = do
      timeout <- jscall "setTimeout(%0, %1)"
                        (JsFn (() -> JS_IO ()) -> Int -> JS_IO Ptr)
                        (MkJsFn f) millis
      pure $ MkTimeout timeout

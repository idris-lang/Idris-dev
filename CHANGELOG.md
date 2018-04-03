# New in 1.3.*

## Language updates
+ Old 'induction' tactics and eliminator generation functionality ('%elim', '%case', 'elim_for') is no longer supported.
  Please, rely on the ones provided by Pruviloj and elaborator reflection instead.

## Library updates

+ Changed rndInt in Effect.Random so that it does not alternate between odd
  and even.
+ Additions to `contrib`:
  * `Data.SortedBag`: Bag (or Multiset) implemention based on `Data.SortedMap`.
  * `Data.PosNat`: A `Nat` paired with a proof that it is positive.
  * `Data.Chain`: A function with an arbitrary number of arguments, plus
    combinators for working with them.

## Tool updates
+ Added a switch `--allow-capitalized-pattern-variables` to optionally allow capitalized pattern variables after they were prohibited in 1.2.0.
+ REPL now prints an error message if program compiled by `:exec` terminates
  abnormally.
+ Idris now builds with GHC 8.4.
+ In the C backend, the representation of Idris values at runtime has been reworked.

# New in 1.2.0

## Language updates

+ In `@`-patterns such as `x@p`, `x` is now in scope on the right-hand side
  of any definitions in `where` clauses, provided the left-hand side of the
  definition does not shadow it.
+ The `LinearTypes` language extension has been revised. It implements the
  rules from Bob Atkey's draft "The Syntax and Semantics of Quantitative
  Type Theory" and now works with holes and case expressions.
+ Backticked operators can appear in sections, e.g. ``(`LTE` 42)`` or
  ``(1 `plus`)``.
+ Backticked operators can have their precendence and associativity set like
  other operators, e.g. ``infixr 8 `cons` ``.  Backticked operators with
  undeclared fixity are treated as non-associative with precedence lower
  than all declared operators.
+ Allow non-injective implementations if explicitly named, e.g.,
  ```idris
  LTB : Nat -> Type
  LTB b = DPair Nat (\ n  => LT n b)

  implementation [uninhabltb] Uninhabited (LTB Z) where
    uninhabited (MkDPair n prf) = absurd prf
  ```
  It is possible to use `using implementation uninhabltb` to add the
  implementation to the automated resolution, but if it fails to find the
  instance due to non-injectivity, one must pass it explicitly to target
  function, i.e. `absurd @{uninhabltb}`.
+ Verbatim strings now support trailing quote characters. All quote characters
  until the final three are considered part of the string. Now a string such as
  `""""hello""""` will parse, and is equivalent to `"\"hello\""`.
+ C FFI now supports pasting in any expression by prefixing it with '#', e.g.
  ```idris
  intMax : IO Int
  intMax = foreign FFI_C "#INT_MAX" (IO Int)
  ```
+ The deprecated keywords `%assert_total`, `abstract`, and `[static]` have
  been removed as well as the use of "public" instead of "public export" to
  expose a symbol.
+ The syntax for pattern-match alternatives now works for `let` statements in
  `do` blocks in addition to `let` expressions and `<-` statements, e.g.
  ```idris
    do …
       let Just x = expr | Nothing => empty
       …
  ```
  This means that a `with`-application (using `|`) cannot be used in that
  position anymore.

## Library Updates

+ Removed `oldeffects` library from `libs` folder, use `effects` or `Control.ST` instead.
+ Added `Text.Literate`, a module for working with literate source files.
+ Added `Data.IORef`, for working with mutable references in `IO` and `JS_IO`.
+ Added `discriminate` and `construct` tactics to Pruviloj.
+ Added `IsSucc` type to `Prelude`, which proves that a `Nat` is a successor.
+ Added `Data.IOArray`, containing primitives for mutable arrays.
+ Added `Language.JSON`, for total serialization/deserialization of JSON data.
+ Reworked operator fixity for many operators.
  * Changed `&&` and `||` to be right-associative. Increased precedence of `&&`
    to be higher than that of `||`.
  * Removed associativity from Boolean comparison operators `==`, `/=`, `<`, `<=`,
    `>`, and `>=`. Increased precedence of `/=` and `==` to match the others.
  * Made `<|>`, `<$>`, and `.` right-associative.
  * Swapped precedence of `<|>` and `<*>` (and its related operators, `<*` and
    `*>`). Now `<|>` has a lower precedence.
  * Lowered the precedence of `>>=` to be below that of `<|>`.
+ Added some useful string manipulation functions to `Data.String.Extra`.
+ Added `Control.Delayed`, a module for conditionally making a type `Inf` or `Lazy`.
+ Added `Data.Fuel`, which implements the `Fuel` data type and the partial `forever` function.
+ Added `Data.Bool.Extra`, a module with properties of boolean operations.
+ Moved core of `Text.Lexer` to `Text.Lexer.Core`. Added several new combinators
  and lexers to `Text.Lexer`.
+ Moved core of `Text.Parser` to `Text.Parser.Core`. Added several new combinators
  to `Text.Parser`. Made the following changes.
  * Flipped argument order of `parse`.
  * Renamed `optional` to `option` and flip argument order.
  * Renamed `maybe` to `optional`.
  * Generalised many combinators to use an unknown `commit` flag where possible.
+ `Prelude.Doubles.atan2` is now implemented as a primitive instead of
  being coded in Idris.
+ Added `Test.Unit` to `contrib` for simple unit testing.
+ Removed several deprecated items from the libraries shipped with Idris.
+ Moved `abs` from the `Neg` interface into its own `Abs` interface.  `Nat`
  implements `Abs` with `abs = id`.
+ Added `Control.ST.File`, an ST based implementation of the same behaviour
  implemented by `Effect.File` in the effects package.

## Tool Updates

+ Private functions are no longer visible in the REPL except for modules
  that are explicitly loaded.
+ The --interface option now creates CommonJS modules on the node backend.
+ The C backend now pass arguments to the C compiler in the same order
  as they were given in the source files.
+ Backslash, braces and percent symbols are now correctly pretty printed
  in LaTeX.
+ Errors and warnings now consistently have the following format:
  ```idris
  reg068.idr:1:6-8:
    |
  1 | data nat : Type where --error
    |      ~~~
  Main.nat has a name which may be implicitly bound.
  This is likely to lead to problems!
  ```
  The code is highlighted when highlighting information is available.  How
  much highlighting information is available depends on where the error
  occurred.
+ The parser provider has been switched from Trifecta to Megaparsec.  This
  could possibly cause some subtle deviations in parsing from previous
  versions of Idris.
+ Many more errors now report beginning *and* ending position (which may be
  on different lines), instead of just a single point.  The format is
  `Foo.idr:9:7-15:` if ending column is on the same line or
  `Foo.idr:9:7-10:15:` if the ending column is on a different line.
+ Error messages were changed so that the last column is inclusive, e.g.
  `Foo.idr:9:7-15:` includes column 15.  Previously the error would have read
  `Foo.idr:9:7-16:`.

## Packaging Updates

+ Package names now only accept a restrictive charset of letters, numbers and the `-_` characters.
  Package names are also case insensitive.
+ When building makefiles for the FFI, the environment variables
  `IDRIS_INCLUDES` and `IDRIS_LDFLAGS` are now set with the correct C
  flags.

# New in 1.1.1

+ Erasure analysis is now faster thanks to a bit smarter constraint solving.
+ Fixed installation issue
+ Fixed a potential segfault when concatenating strings

# New in 1.1.0

## Library Updates

+ Added `Text.PrettyPrint.WL` an implementation of the Wadler-Leijen
  Pretty-Print algorithm.  Useful for those wishing to pretty print
  things.
+ Added `Text.Lexer` and `Text.Parser` to `contrib`. These are small libraries
  for implementing total lexical analysers and parsers.
+ New instances:
    + Added `Catchable` for `ReaderT`, `WriterT`, and `RWST`.
    + Added `MonadTrans` for `RWST`.
+ Added utility functions to `Data.SortedMap` and `Data.SortedSet` (`contrib`),
  most notably `merge`, merging two maps by their `Semigroup` op (`<+>`)
+ `Prelude.WellFounded` now contains an interface `Sized a` that defines a size
  mapping from `a` to `Nat`. For example, there is an implementation for lists,
  where `size = length`.

  The function `sizeAccessible` then proves well-foundedness of the relation
  `Smaller x y = LT (size x) (size y)`, which  allows us to use strong
  induction conveniently with any type that implements `Sized`.

  In practice, this allows us to write functions that recurse not only on
  direct subterms of their arguments but on any value
  with a (strictly) smaller `size`.

  A good example of this idiom at work is `Data.List.Views.splitRec` from `base`.
+ Added utility lemma `decEqSelfIsYes : decEq x x = Yes Refl` to
  `Decidable.Equality`. This is primarily useful for proving properties of
  functions defined with the help of `decEq`.

## Tool Updates

+ New JavaScript code generator that uses an higher level intermediate
  representation.

+ Various optimizations of the new JavaScript code generator.

+ Names are now annotated with their representations over the IDE
  protocol, which allows IDEs to provide commands that work on special
  names that don't have syntax, such as case block names.


# New in 1.0

+ It's about time

# New in 0.99.2

## Library Updates

+ Added `Data.Buffer` to `base`. This allows basic manipulation of mutable
  buffers of `Bits8`, including reading from and writing to files.

## Tool Updates

+ Idris now checks the list of packages specified at the command line
  against those installed. If there is a mismatch Idris will complain.

## Miscellaneous Updates

+ Documentation updates for the new `Control.ST` library
+ Various stability/efficiency fixes

# New in 0.99.1:

## Language updates

* Language pragmas now required for the less stable existing features, in
  addition to the existing `TypeProviders` and `ErrorReflection`:
  + `ElabReflection`, which must be enabled to use `%runElab`
  + `UniquenessTypes`, which must be enabled to use `UniqueType`
  + `DSLNotation`, which must be enabled to define a `dsl` block
  + `FirstClassReflection`, which must be enabled to define a `%reflection`
    function

* New language extension `LinearTypes`:
  + This allows adding a /multiplicity/ to a binder which says how often it
    is allowed to be used; either 0 or 1 (if unstated, multiplicity is "many")
  + The typing rules follow Conor McBride's paper "I Got Plenty o' Nuttin'"
  + This is highly experimental, unfinished, not at all polished. and there
    are still lots of details to sort out. Some features don't quite work
    properly yet. But it is there to play with for the brave!

## Tool Updates

+ Idris' output has been updated to more accurately reflect its
  progress through the compiler i.e. Type Checking; Totality Checking;
  IBC Generation; Compiling; and Code Generation. To control the
  loudness of the reporting three verbosity levels are introduced:
  `--V0`, `--V1`, and `--V2`. The old aliases of `-V` and `--verbose`
  persist.

+ New REPL command `:!` that runs an external shell command.

+ The REPL now colourises output on MinTTY consoles (e.g., Cygwin and MSYS)
  on Windows, which previously did not occur due to a bug.

+ Idris now runs in a UTF-8-compatible codepage on Windows. This fixes many
  Unicode-rendering issues on Windows (e.g., error messages stating
  `commitBuffer: invalid argument (invalid character)`).

+ Idris now has a `--warnipkg` flag to enable auditing of Idris
  packages during build time. Currently auditing check's the list of
  modules specified in the `iPKG` file with those presented in the
  package directory.

## Library Updates

+ Terminating programs has been improved with more appropriate
  functions (`exitWith`, `exitFailure`, and `exitSuccess`) and a data
  structure (`ExitCode`) to capture a program's return code.
+ Casting a `String` to an `Int`, `Integer` or a `Double` now ignores leading
  and trailing whitespace. Previously only leading whitespace was ignored.
+ RTS functions `openFile`, `do_popen`, and `ARGV` are now properly encoded using UTF-8 on Windows.

# New in 0.99:

## Language updates

* `record` syntax now allows updating fields, including nested fields,
  by applying a function using the `$=` operator.  For example:

  ```idris
  record Score where
         constructor MkScore
         correct : Nat
         attempted : Nat

  record GameState where
         constructor MkGameState
         score : Score
         difficulty : Nat

  correct : GameState -> GameState
  correct st = record { score->correct $= (+1),
                        score->attempted $= (+1) } st
  ```

* Implicit parameter to interfaces are now allowed. For example:

  ```idris
  interface Shows (ts : Vect k Type) where
    shows : HVect ts -> Vect k String
  ```
  In this interface, `k` is an implicit parameter, but previously needed to
  be explicit


## Library updates

* The File Effect has been updated to take into account changes in
  `Prelude.File` and to provide a 'better' API.
* `natEnumFromThen` and `natEnumFromTo` have been updated to correctly calculate reverse ranges. Range syntax `[a,b..c]` now can be used again to generate reverse ranges.
* `divBN` and `modBN` now can only be used for unsigned numbers.
* `return`, which has been an alias for `pure` for many releases, is now deprecated.
* Replace instance with implementation:
  + `InstanceN` is deprecated, use `ImplementationN` instead.
  + `InstanceCtorN` is deprecated, use `ImplementationCtorN` instead.
  + `addInstance` is deprecated, use `addImplementation` instead.
  + `%instance` keyword is deprecated, use `%implementation` instead.

* Idris packages are now installed within a sub-directory `libs` of Idris' data directory, before they were installed in the directory's root.

## Tool updates

* Idris' documentation system now displays the documentation for auto
  implicits in the output of `:doc`. This is tested for in `docs005`.
* New command line flag `--info` that displays information about the installation.
* New command line flag `--sourcepath <dir>` that allows adding directories to the source search path.
* Allow 'installation' of a package's IdrisDoc documentation into a central location. The default location is the subdirectory `docs` of Idris' data directory.
  * New flag `--installdoc <ipkg>` provided to install documentation
  * New flag `--docdir` provided to show default documentation installation location.
  * New environment variable `IDRIS_DOC_PATH` to allow specification of an alternative installation path for documentation.
* Semantic meaning behind several environment variables has been clarified in documentation and code. See compilation section of the reference manual for more details.
* Interface parameter constraints are now printed in the output of `:doc`. This
  is tested for in `docs006`.

## Miscellaneous updates

* New, faster, better, implementation of the coverage checker
* The test suite now uses [tasty-golden](https://hackage.haskell.org/package/tasty-golden). New tests must be registered in `test/TestData.hs`, as explained in the relevant `README.md`.
* Added OSX and Windows continous integration with Travis and Appveyor.

## UI Changes

* The :e command can now handle an $EDITOR with arguments in it, like "emacs -nw"


# New in 0.12:

## Language updates

* `rewrite` can now be used to rewrite equalities on functions over
  dependent types
* `rewrite` can now be given an optional rewriting lemma, with the syntax
  `rewrite [rule] using [rewrite_lemma] in [scope]`.

* Reorganised elaboration of `implementation`, so that interfaces with
  dependencies between methods now work more smoothly

* Allow naming of parent implementations when defining an implementation.
  For example:

  ```
  [PlusNatSemi] Semigroup Nat where
    (<+>) x y = x + y

  [MultNatSemi] Semigroup Nat where
    (<+>) x y = x * y

  -- use PlusNatSemi as the parent implementation
  [PlusNatMonoid] Monoid Nat using PlusNatSemi where
    neutral = 0

  -- use MultNatSemi as the parent implementation
  [MultNatMonoid] Monoid Nat using MultNatSemi where
    neutral = 1
  ```

* Interface definitions can now include data declarations (but not data
  definitions). Any implementation of the interface must define the method
  using a data type. The effect is to cause Idris to treat the method as
  a data type (for unification and interface resolution purposes).

* Experimentally, allow named implementations to be available by default in a
  block of declarations with `using` notation. For example:

  ```
  using implementation PlusNatMonoid
    test : Nat -> Nat
    test x = x <+> x <+> neutral
  ```

* Constraint arguments can now appear anywhere in function types, not just
  at the top level or after an implicit argument binding.

* Experimental extended `with` syntax, which allows calling functions defined
  in a with block directly. For example:

  ```
  data SnocList : List a -> Type where
       Empty : SnocList []
       Snoc : SnocList xs -> SnocList (xs ++ [x])

  snocList : (xs : List a) -> SnocList a

  my_reverse : List a -> List a
  my_reverse xs with (snocList xs)
    my_reverse [] | Empty = []
    my_reverse (ys ++ [x]) | (Snoc p) = x :: my_reverse ys | p
  ```

    The `| p` on the right hand side means that the `with` block function will
    be called directly, so the recursive structure of `SnocList` can direct the
    recursion structure of `my_reverse`.

* Added `%fragile` directive, which gives a warning and a message when a
  fragile name is referenced. For use in detailing fragile APIs.

* The totality checker now looks under `case` blocks, rather than treating
  them as mutually defined functions with their top level function, meaning
  that it can spot more total functions.

* The totality checker now looks under `if...then...else` blocks when checking
  for productivity.

* The `%assert_total` directive is now deprecated. Instead, you can
  use one of the functions `assert_total`, `assert_smaller` or
  `assert_unreachable` to describe more precisely where a totality assertion
  is needed.

## Library updates

* `Control.WellFounded` module removed, and added to the Prelude as
  `Prelude.WellFounded`.
* Added `Data.List.Views` with views on `List` and their covering functions.
* Added `Data.Nat.Views` with views on `Nat` and their covering functions.
* Added `Data.Primitives.Views` with views on various primitive types and their covering functions.
* Added `System.Concurrency.Sessions` for simple management of conversations
  between processes

## iPKG Updates

* Taking cues from cabal, the `iPKG` format has been extended to
  include more package metadata information.  The following fields
  have been added:

  + `brief`: Brief description of the package.
  + `version`: Version string to associate with the package.
  + `readme`: Location of the README file.
  + `license`: Description of the licensing information.
  + `author`: Author information.
  + `maintainer`: Maintainer information.
  + `homepage`: Website associated with the package.
  + `sourcepage`: Location of the DVCS where the source can be found.


## Miscellaneous updates

* The Idris man page is now installed as part of the cabal/stack build  process.

* Improved startup performance by reducing the processing of an already imported
  module that has changed accessibility.

* A limited set of command line options can be used to override
  package declared options. Overridable options are currently, logging
  level and categories, default totality check, warn reach, IBC output
  folder, and idris path. Note overriding IBC output folder, only
  affects the installation of Idris packages.

* Remove deprecated options `--ideslave` and `--ideslave-socket`. These options
  were replaced with `--ide-mode` and `--ide-mode-socket` in 0.9.17

* The code generator output type `MavenProject` was specific to the
  Java codegen and has now been deprecated, together with the
  corresponding `--mvn` option.

* Definitional equality on Double is now bit-pattern identity rather
  than IEEE's comparison operator. This prevents a bug where programs
  could distinguish between -0.0 and 0.0, but the type theory could
  not, leading to a contradiction. The new fine-grained equality
  prevents this.

* Naming conventions for Idris packages in an iPKG file now follow the
  same rules for executables.  Unquoted names must be valid namespaced
  Idris identifiers e.g. ``package my.first.package``. Quoted package
  names allow for packages to be given valid file names, for example,
  ``package "my-first-package"``.

## Reflection changes

* The implicit coercion from String to TTName was removed.

* Decidable equality for TTName is available.

# New in 0.11

## Updated export rules

* The export rules are:
  - 'private' means that the definition is not exported at all
  - 'export' means that the top level type is exported, but not the
    definition. In the case of 'data', this means the type constructor is
    exported but not the data constructors.
  - 'public export' means that the entire definition is exported.
* By default, names are 'private'. This can be altered with an %access directive
  as before.
* Exported types can only refer to other exported names
* Publicly exported definitions can only refer to publicly exported names

## Improved C FFI

* Idris functions can now be passed as callbacks to C functions or wrapped in a
  C function pointer.
* C function pointers can be called.
* Idris can access pointers to C globals.

## Effects

* Effects can now be given in any order in effect lists (there is no need for
  the ordering to be preserved in sub lists of effects)

## Elaborator reflection updates

* Datatypes can now be defined from elaborator reflection:
  - declareDatatype adds the type constructor declaration to the context
  - defineDatatype adds the constructors to the datatype
  - To declare an inductive-recursive family, declare the types of the function
    and the type constructor before defining the pattern-match cases and
    constructors.

## Minor language changes

* The `[static]` annotation is changed to `%static` to be consistent with the
  other annotations.
* Added `%auto_implicits` directive. The default is `%auto_implicits on`.
  Placing `%auto_implicits off` in a source file means that after that point,
  any implicit arguments must be bound, e.g.:

  ```
  append : {n,m,a:_} -> Vect n a -> Vect m a -> Vect (n + m) a
  ```

  Only names which are used explicitly in the type need to be bound, e.g.:

  ```
  Here  : {x, xs : _} -> Elem x (x :: xs)
  ```

  In `Here`, there is no need to bind any of the variables in the type of `xs`
  (it could be e.g. `List a` or `Vect n a`; `a` and `n` will still be implicitly
  bound).

  You can still implicitly bind with 'using':

   ```
    using (xs : Vect _ _)
      data Elem  : {a, n : _} -> a -> Vect n a -> Type where
           Here  : {x : _} -> Elem x (x :: xs)
           There : {x, y : _} -> Elem x xs -> Elem x (y :: xs)
   ```

  However, note that *only* names which appear in *both* the using block
  *and* the type being defined will be implicitly bound. The following will
  therefore fail because 'n' isn't implicitly bound:

  ```
    using (xs : Vect n a)
      bad : Elem x xs -> Elem x (y :: xs)
  ```

* `Sigma` has been renamed  to `DPair`.
* Accessor functions for dependent pairs have been renamed to bring them into
  line with standard accessor functions for pairs. The function `getWitness` is
  now `fst`, and `getProof` is `snd`.
* File Modes expanded: Append, ReadWriteTruncate, and ReadAppend added, Write is
  deprecated and renamed to WriteTruncate.
* C11 Extended Mode variations added to File Modes.
* More flexible holes. Holes can now depend on other holes in a term (such as
  implicit arguments which may be inferred from the definition of the hole).
* Programs with holes can now be compiled.  Attempting to evaluate an expression
  with a hole results in a run time error.
* Dependent pairs now can be specified using a telescope-style syntax, without
  requirement of nesting, e.g. it is possible to now write the following:

  ```
    (a : Type ** n : Nat ** Vect n a)
  ```

* Idris will give a warning if an implicit is bound automatically, but would
  otherwise be a valid expressio if the name was used as a global

## External Dependencies

* Curses has been removed as an external dependency.

# New in 0.10

* `class` and `instance` are now deprecated keywords. They have been replaced by
  `interface` and `implementation` respectively. This is to properly reflect
  their purpose.
* `(/)` operator moved into new Fractional interface.
* Idris' logging infrastructure has been categorised. Command line and repl are
  available. For command line the option `--logging-categories CATS` is used to
  pass in the categories. Here `CATS` is a colon separated quoted string
  containing the categories to log. The REPL command is `logcats CATS`.  Where
  `CATS` is a whitespace separated list of categoriese. Default is for all
  categories to be logged.
* New flag `--listlogcats` to list logging categories.

# New in 0.9.20

## Language updates

* Improved unification by implementing a pattern unification rule
* The syntax `` `{{n}}`` quotes n without resolving it, allowing short syntax for
  defining new names. `` `{n}`` still quotes n to an existing name in scope.
* A new primitive operator `prim__strSubstr` for more efficient extraction of
  substrings. External code generators should implement this.
* The previous syntax for tactic proofs and the previous interactive prover are
  now deprecated in favour of reflected elaboration. They will be removed at
  some point in the future.
* Changed scoping rules for unbound implicits: any name which would be a valid
  unbound implicit is now *always* an unbound implicit. This is much more
  resilient to changes in inputs, but does require that function names be
  explicitly qualified when in argument position.
* Name binding in patterns follows the same rule as name binding for implicits
  in types: names which begin with lower case letters, not applied to any
  arguments, are treated as bound pattern variables.
* Added `%deprecate` directive, which gives a warning and a message when a
  deprecated name is referenced.

## Library updates

* The `Neg` class now represents numeric types which can be negative. As such,
  the `(-)` operator and `abs` have been moved there from `Num`.
* A special version of `(-)` on `Nat` requires that the second argument is
  smaller than or equal to the first. `minus` retains the old behaviour,
  returning `Z` if there is an underflow.
* The `(+)`, `(-)`, and `(*)` operations on Fin have been removed.
* New Logging Effects have been added to facilitate logging of effectful
  programmes.
* Elaborator reflection is now a part of the prelude. It is no longer necessary
  to import `Language.Reflection.Elab`.
* The `PERF` effect allows for simple performance metrics to be collected from
  Effectful programs.
* Some constructors that never actually occurred have been removed from the `TT`
  and `Raw` reflection datatypes in Language.Reflection.
* File `IO` operations (for example openFile/fread/fwrite) now return
  `Either FileError ty` where the return type was previously `ty` to indicate
  that they may fail.

## Tool updates

* Records are now shown as records in `:doc`, rather than as the underlying
  datatype
* iPKG files have a new option `pkgs` which takes a comma-separated list of
  package names that the idris project depends on. This reduces bloat in the
  `opts` option with multiple package declarations.
* iPKG files now allow `executable = "your filename here"` in addition to the
  Existing `Executable = yourFilenameHere` style. While the unquoted version is
  limited to filenames that look like namespaced Idris identifiers
  (`your.filename.here`), the quoted version accepts any valid filename.
* Add definition command (`\d` in Vim, `Ctrl-Alt-A` in Atom, `C-c C-s` in Emacs)
  now adds missing clauses if there is already a definition.

## Miscellaneous updates

* Disable the deprecation warnings for %elim and old-style tactic scripts with
  the `--no-elim-deprecation-warnings` and `--no-tactic-deprecation-warnings`
  flags.

# New in 0.9.19

* The Idris Reference manual has been fleshed out with content originally found
  on the GitHub wiki.
* The `Show` class has been moved into `Prelude.Show` and augmented with the
  method `showPrec`, which allows correct parenthesization of showed terms. This
  comes with the type `Prec` of precedences and a few helper functions.
* New REPL command `:printerdepth` that sets the pretty-printer to only descend
  to some particular depth when printing. The default is set to a high number to
  make it less dangerous to experiment with infinite structures. Infinite depth
  can be set by calling :printerdepth with no argument.
* Compiler output shows applications of `>>=` in do-notation
* `fromInteger i` where `i` is an integer constant is now shown just as `i` in
  compiler output
* An interactive shell, similar to the prover, for running reflected elaborator
  actions. Access it with `:elab` from the REPL.
* New command-line option `--highlight` that causes Idris to save highlighting
  information when successfully type checking. The information is in the same
  format sent by the IDE mode, and is saved in a file with the extension ".idh".
* Highlighting information is saved by the parser as well, allowing it to
  highlight keywords like `case`, `of`, `let`, and `do`.
* Use predicates instead of boolean equality proofs as preconditions on `List`
  functions
* More flexible 'case' construct, allowing each branch to target different
  types, provided that the case analysis does not affect the form of any
  variable used in the right hand side of the case.
* Some improvements in interactive editing, particularly in lifting out
  definitions and proof search.
* Moved `System.Interactive`, along with `getArgs` to the Prelude.
* Major improvements to reflected elaboration scripts, including the ability to run
  them in a declaration context and many bug fixes.
* `decl syntax` rules to allow syntax extensions at the declaration level
* Experimental Windows support for console colours

# New in 0.9.18:

* GHC 7.10 compatibility
* Add support for bundled toolchains.
* Strings are now UTF8 encoded in the default back end
* Idris source files are now assumed to be in UTF8, regardless of locale
  settings.
* Some reorganisation of primitives:
  + `Buffer` and `BitVector` primitives have been removed (they were not tested
    sufficiently, and lack a maintainer)
  + `Float` has been renamed `Double` (`Float` is defined in the Prelude for
    compatibility)
  + Externally defined primitives and operations now supported with `%extern`
    directive, allowing back ends to define their own special purpose primitives
  + `Ptr` and `ManagedPtr` have been removed and replaced with external primitives
* Add `%hint` function annotation, which allows functions to be used as hints in
  proof search for `auto` arguments. Only functions which return an instance of
  a data or record type are allowed as hints.
* Syntax rules no longer perform variable capture. Users of effects will need to
  explicitly name results in dependent effect signatures instead of using the
  default name `result`.
* Pattern-matching lambdas are allowed to be impossible. For example,
  `Dec (2 = 3)` can now be constructed with `No $ \(Refl)` impossible, instead of
  requiring a separate lemma.
* Case alternatives are allowed to be impossible:

  ```
  case Vect.Nil {a=Nat} of { (x::xs) impossible ; [] => True }
  ```

* The default `Semigroup` and `Monoid` instances for Maybe are now prioritised
  choice, keeping the first success as Alternative does. The version that
  collects successes is now a named instance.
* `:exec` REPL command now takes an optional expression to compile and run/show
* The return types of `Vect.findIndex`, `Vect.elemIndex` and `Vect.elemIndexBy`
  were changed from `Maybe Nat` to `Maybe (Fin n)`
* A new `:browse` command shows the contents of a namespace
* `` `{n}`` is syntax for a quotation of the reflected representation
  of the name `n`. If `n` is lexically bound, then the resulting
  quotation will be for it, whereas if it is not, then it will succeed
  with a quotation of the unique global name that matches.
* New syntax for records that closely matches our other record-like structures:
  type classes. See the updated tutorial for details.
* Records can be coinductive. Define coinductive records with the `corecord`
  keyword.
* Type class constructors can be assigned user-accessible names. This is done
  using the same syntax as record constructors.
* `if ... then ... else ...` is now built-in syntax instead of being defined in
  a library. It is shown in REPL output and error messages, rather than its
  desugaring.
* The desugaring of `if ... then ... else ...` has been renamed to `ifThenElse`
  from `boolElim`. This is for consistency with GHC Haskell and
  scala-virtualized, and to reflect that if-notation makes sense with non-Bool
  datatypes.
* Agda-style semantic highlighting is supported over the IDE protocol.
* Experimental support for elaborator reflection. Users can now script the
  elaborator, for use in code generation and proof automation. This feature is
  still under rapid development and is subject to change without notice. See
  Language.Reflection.Elab and the %runElab constructs

# New in 0.9.17

* The `--ideslave` command line option has been replaced with a `--ide-mode`
  command line option with the same semantics.
* A new tactic `claim N TY` that introduces a new hole named `N` with type `TY`
* A new tactic `unfocus` that moves the current hole to the bottom of the
  hole stack
* Quasiquotation supports the generation of `Language.Reflection.Raw` terms in
  addition to `Language.Reflection.TT`. Types are used for disambiguation,
  defaulting to `TT` at the REPL.
* `Language.Reflection.Quotable` now takes an extra type parameter which
  determines the type to be quoted to. Instances are provided to quote common
  types to both `TT` and `Raw`.
* Library operators have been renamed for consistency with Haskell. In
  particular, `Applicative.(<$>)` is now `Applicative.(<*>)` and `(<$>)` is now
  an alias for Functor.map. Correspondingly, ($>) and (<$) have been renamed to
  `(<*)` and `(*>)`. The cascading effects of this rename are that
  `Algebra.(<*>)` has been renamed to `Algebra.(<.>)` and `Matrix.(<.>)` is now
  `Matrix.(<:>)`.
* Binding forms in DSL notation are now given an extra argument: a reflected
  representation of the name that the user chose.  Specifically, the rewritten
  `lambda`, `pi`, and `let` binders will now get an extra argument of type
  `TTName`. This allows more understandable dynamic errors in DSL code and more
  readable code generation results.
* DSL notation can now be applied with `$`
* Added `FFI_Export` type which allows Idris functions to be exportoed and
  called from foreign code
* Instances can now have documentation strings.
* Type providers can have documentation strings.
* Unification errors now (where possible) contain information about provenance
  of a type
* New REPL command `:core TM` that shows the elaborated form of `TM` along with
  its elaborated type using the syntax of `TT`. IDE mode has a corresponding
  command `:elaborate-term` for serialized terms.
* Effectful and IO function names for sending data to STDOUT have been
  aligned, semantically.
    + `print` is now for putting showable things to STDOUT.
    + `printLn` is for putting showable things to STDOUT with a new line
    + `putCharLn` for putting a single character to STDOUT, with a new line.
* Classes can now be annotated with 'determining parameters' to say which must
  be available before resolving instances. Only determining parameters are
  checked when checking for overlapping instances.
* New package `contrib` containing things that are less mature or less used than
  the contents of `base`. `contrib` is not available by default, so you may need
  to add `-p contrib` to your .ipkg file or Idris command line.
* Arguments to class instances are now checked for injectivity.  Unification
  assumes this, so we need to check when instances are defined.

# New in 0.9.16

* Inductive-inductive definitions are now supported (i.e. simultaneously defined
  types where one is indexed by the other.)
* Implicits and type class constraints can now appear in scopes other than the
  top level.
* Importing a module no longer means it is automatically reexported. A new
  `public` modifier has been added to import statements, which will reexport the
  names exported from that module.
* Implemented `@`-patterns. A pattern of the form `x@p` on the left hand side
  matches `p`, with `x` in scope on the right hand side with value `p`.
* A new tactic sourceLocation that fills the current hole with the current
  source code span, if this information is available. If not, it raises an
  error.
* Better Unicode support for the JavaScript/Node codegen
* `:search` and `:apropos` commands can now be given optional package lists to
  search.
* `Vect`, `Fin` and `So` moved out of prelude into `base`, in modules
  `Data.Vect`, `Data.Fin` and `Data.So` respectively.
* Several long-standing issues resolved, particularly with pattern matching and
  coverage checking.
* Modules can now have API documentation strings.

# New in 0.9.15

* Two new tactics: `skip` and `fail`. Skip does nothing, and fail takes a string
  as an argument and produces it as an error.
* Corresponding reflected tactics `Skip` and `Fail`. Reflected `Fail` takes a
  list of `ErrorReportParts` as an argument, like error handlers produce,
  allowing access to the pretty-printer.
* Stop showing irrelevant and inaccessible internal names in the interactive
  prover.
* The proof arguments in the `List` library functions are now implicit and
  solved automatically.
* More efficient representation of proof state, leading to faster elaboration of
  large expressions.
* *EXPERIMENTAL* Implementation of uniqueness types
* Unary negation now desugars to `negate`, which is a method of the `Neg` type
  class.  This allows instances of `Num` that can't be negative, like `Nat`, and
  it makes correct IEEE Float operations easier to encode. Additionally, unary
  negation is now available to DSL authors.
* The Java and LLVM backends have been factored out for separate
  maintenance. Now, the compiler distribution only ships with the C and
  JavaScript backends.
* New REPL command `:printdef` displays the internal definition of a name
* New REPL command `:pprint` pretty-prints a definition or term with LaTeX or
  HTML highlighting
* Naming of data and type constructors is made consistent across the standard
  library (see #1516)
* Terms in `code blocks` inside of documentation strings are now parsed and type
  checked. If this succeeds, they are rendered in full color in documentation
  lookups, and with semantic highlighting for IDEs.
* Fenced code blocks in docs defined with the "example" attribute are rendered
  as code examples.
* Fenced code blocks declared to be Idris code that fail to parse or type check
  now provide error messages to IDE clients.
* *EXPERIMENTAL* support for partial evaluation (Scrapping your Inefficient
  Engine style)

# New in 0.9.14

* Tactic for case analysis in proofs
* Induction and case tactic now work on expressions
* Support for running tests for a package with the tests section of .ipkg files
  and the `--testpkg` command-line option
* Clearly distinguish between type providers and postulate providers at the use
  site
* Allow dependent function syntax to be overridden in dsl blocks, similarly to
  functions and let. The keyword for this is `pi`.
* Updated `effects` library, with simplified API
* All new JavaScript backend (avoids callstack overflows)
* Add support for `%lib` directive for NodeJS
* Quasiquotes and quasiquote patterns allow easier work with reflected
  terms.  `` `(EXPR)`` quasiquotes EXPR, causing the elaborator to be
  used to produce a reflected version of it. Subterms prefixed with `~`
  are unquoted - on the RHS, they are reflected terms to splice in,
  while on the LHS they are patterns.

  A quasiquote expression can be given a goal type for the elaborator,
  which helps with disambiguation. For instance, `` `(() : ())``
  quotes the unit constructor, while `` `(() : Type)`` quotes the unit
  type.  Both goal types and quasiquote are typechecked in the global
  environment.
* Better inference of unbound implicits

# New in 0.9.13

* IDE support for retrieving structured information about metavariables
* Experimental Bits support for JavaScript
* IdrisDoc: a Haddock- and JavaDoc-like HTML documentation generator
* Command line option `-e` (or `--eval`) to evaluate expressions without loading
  the REPL. This is useful for writing more portable tests.
* Many more of the basic functions and datatypes are documented.
* Primitive types such as Int and String are documented
* Removed javascript lib in favor of idris-hackers/iQuery
* Specify codegen for :compile REPL command (e.g. `:compile` javascript
  program.js)
* Remove `:info` REPL command, subsume and enhance its functionality in the `:doc` command
* New (first class) nested record update/access syntax:

  ```
  record { a->b->c = val } x -- sets field accessed by c (b (a x)) to val
  record { a->b->c } x -- accesses field, equivalent to c (b (a x))
  ```

* The banner at startup can be suppressed by adding `:set` nobanner to the initialisation script.
* `:apropos` now accepts space-delimited lists of query items, and searches for
  the conjunction of its inputs. It also accepts binder syntax as search
  strings - for instance, `->` finds functions.
* Totality errors are now treated as warnings until code generation time, when
  they become errors again. This allows users to use the interactive editing
  features to fix totality issues, but no programs that violate the stated
  assumptions will actually run.
* Added `:makelemma` command, which adds a new top level definition to solve a
  metavariable.
* Extend `:addclause` to add instance bodies as well as definitions
* Reverse parameters to `BoundedList` -- now matches `Vect`, and is easier to
  instantiate classes.
* Move `foldl` into Foldable so it can be overridden.
* Experimental `:search` REPL command for finding functions by type

## Internal changes

* New implementation of erasure

# New in 0.9.12

* Proof search now works for metavariables in types, giving some interactive
  type inference.
* New `Lazy` type, replacing laziness annotations.
* JavaScript and Node codegen now understand the `%include` directive.
* Concept of `null` is now understood in the JavaScript and Node codegen.
* Lots of performance patches for generated JavaScript.
* New commands `:eval` (`:e`) and `:type` (`:t`) in the prover, which either
  normalise or show the type of expressions.
* Allow type providers to return postulates in addition to terms.
* Syntax for dealing with match failure in `<-` and pattern matching let.
* New syntax for inline documentation. Documentation starts with `|||`, and
  arguments are documented by preceding their name with `@`. Example:

  ```
  ||| Add two natural numbers
  ||| @ n the first number (examined by the function)
  ||| @ m the second number (not examined)
  plus (n, m : Nat) -> Nat
  ```

* Allow the auto-solve behaviour in the prover to be disabled, for easier
  debugging of proof automation. Use `:set autosolve` and `:unset autosolve`.
* Updated `effects` library
* New `:apropos` command at REPL to search documentation, names, and types
* Unification errors are now slightly more informative
* Support mixed induction/coinduction with `Inf` type
* Add `covering` function option, which checks whether a function and all
  descendants cover all possible inputs

# New in 0.9.11

* Agda-style equational reasoning (in Syntax.PreorderReasoning)
* 'case' construct now abstracts over the scrutinee in its type
* Added label type 'name (equivalent to the empty type).  This is intended for
  field/effect disambiguation. "name" can be any valid identifier. Two labels
  are definitionally equal if they have the same name.
* General improvements in error messages, especially %error_reverse annotation,
  which allows a hint as to how to display a term in error messages
* `--ideslave` mode now transmits semantic information about many of the strings
  that it emits, which can be used by clients to implement semantic highlighting
  like that of the REPL. This has been implemented in the Emacs mode and the IRC
  bot, which can serve as examples.
* New expression form: `with NAME EXPR` privileges the namespace `NAME` when
  disambiguating overloaded names. For example, it is possible to write `with
  Vect [1,2,3]` at the REPL instead of `the (Vect _ _) [1,2,3]`, because the
  `Vect` constructors are defined in a namespace called `Vect`.
* `assert_smaller` internal function, which marks an expression as smaller than
  a pattern for use in totality checking.  e.g. `assert_smaller (x :: xs) (f
  xs)` asserts that `f xs` will always be structurally smaller than `(x :: xs)`
* `assert_total` internal function, which marks a subexpression as assumed to be
  total, e.g `assert_total (tail (x :: xs))`.
* Terminal width is automatically detected if Idris is compiled with curses
  support. If curses is not available, automatic mode assumes 80 columns.
* Changed argument order for `Prelude.Either.either`.
* Experimental `neweffects'`library, intended to replace `effects` in the next
  release.

## Internal changes

* Faster elaboration
* Smaller .ibc files
* Pretty-printer now used for all term output

# New in 0.9.10

* Type classes now implemented as dependent records, meaning that method types
  may now depend on earlier methods.
* More flexible class instance resolution, so that function types and lambda
  expressions can be made instances of a type class.
* Add `!expr` notation for implicit binding of intermediate results in
  monadic/do/etc expressions.
* Extend Effects package to cope with possibly failing operations, using
  `if_valid`, `if_error`, etc.
* At the REPL, `it` now refers to the previous expression.
* Semantic colouring at the REPL. Turn this off with `--nocolour`.
* Some prettifying of error messages.
* The contents of `~/.idris/repl/init` are run at REPL start-up.
* The REPL stores a command history in `~/.idris/repl/history`.
* The `[a..b]`, `[a,b..c]`, `[a..]`, and `[a,b..]` syntax now pass the totality
  checker and can thus be used in types. The `[x..]` syntax now returns an
  actually infinite stream.
* Add `%reflection` option for functions, for compile-time operations on syntax.
* Add expression form `quoteGoal x by p in e` which applies `p` to the expected
  expression type and binds the result to `x` in the scope `e`.
* Performance improvements in Strings library.
* Library reorganisation, separated into `prelude/` and `base/`.

## Internal changes

* New module/dependency tree checking.
* New parser implementation with more precise errors.
* Improved type class resolution.
* Compiling Nat via GMP integers.
* Performance improvements in elaboration.
* Improvements in termination checking.
* Various REPL commands to support interactive editing, and a client/server
  mode to allow external invocation of REPL commands.

# New in 0.9.9

## User visible changes

* Apply functions by return type, rather than with arguments: `t <== f` means
  "apply f with arguments such that it returns a value of type t"
* Allow the result type of a rewrite to be specified
* Allow names to be attached to provisional definitions lhs `?= {name} rhs` --
  generates a lemma called `name` which makes the types of the lhs and rhs
  match. `{name}` is optional - a unique name is generated if it is absent.
* Experimental LLVM backend
* Added `Data.HVect` module
* Fix `fromInteger` to take an `Integer`, rather than an `Int`
* Integer literals for `Fin`
* Renamed `O` to `Z`, and `fO` to `fZ`
* Swapped `Vect` arguments, now `Vect : Nat -> Type -> Type`
* Added `DecEq` instances
* Add `equiv` tactic, which rewrites a goal to an equivalent (convertible) goal

##  Internal changes

* Add annotation for unification traces
* Add `mrefine` tactic for refining by matching against a type
* Type class resolution fixes
* Much faster coverage checking

# New in 0.9.8

## User visible changes

* Added `rewrite ... in ...` construct
* Allow type class constraints in `using` clauses
* Renamed `EFF` to `EFFECT` in Effect package
* Experimental Java backend
* Tab completion in REPL
* Dynamic loading of C libraries in the interpreter
* Testing IO actions at the REPL with `:x` command
* Improve rendering of `:t`
* Fixed some INTERNAL ERROR messages

## Internal Changes

* Fix non-linear pattern checking
* Improved name disambiguation
* More flexible unification and elaboration of lambdas
* Various unification and totality checking bug fixes

# New in 0.9.7

## User visible changes

* `implicit` keyword, for implicit type conversion
* Added Effects package
* Primitives for 8,16,32 and 64 bit integers

## Internal Changes

* Change unification so that it keeps track of failed constraints in case
  later information helps to resolve them
* Distinguishing parameters and indices in data types
* Faster termination/coverage checking
* Split 'javascript' target into 'javascript' and 'node'

# New in 0.9.6

## User visible changes

* The type of types is now `Type` rather than `Set`
* Forward declarations of data allowed
  - supporting induction recursion and mutually recursive data
* Type inference of definitions in `where` clauses
  - Provided that the type can be completely determined from the first
    application of the function (in the top level definition)
* `mutual` blocks added
  - effect is to elaborate all types of declarations in the block before
    elaborating their definitions
  - allows inductive-recursive definitions
* Expression inspected by `with` clause now abstracted from the goal
  - i.e. "magic" with
* Implicit arguments will be added automatically only if their initial letter is
  lower case, or they are in a using declaration
* Added documentation comments (Haddock style) and `:doc` REPL command
* Pattern matching on strings, big integers and characters
* Added `System.Concurrency` modules
* Added `postulate` declarations
* Allow type annotations on `let` tactic
* EXPERIMENTAL JavaScript generation, with `--target javascript` option

## Internal Changes

* Separate inlining methods at compile-time and run-time
* Fixed nested parameters blocks
* Improve efficiency of elaborator by:
   - only normalising when necessary
   - reducing backtracking with resolving ambiguities
* Better compilation of case trees

# New in 0.9.5

## User visible changes

* Added codata
  - as data declarations, but constructor arguments are evaluated lazily
  - functions which return a codata type do not reduce at compile time
* Added `parameters` blocks
* Allow local data definitions in where blocks
* Added `%default` directive to declare total-by-default or partial-by-default
  for functions, and a corresponding "partial" reserved words to mark functions
  as allowed to be partial. Also `--total` and `--partial` added as command line
  options.
* Command line option `--warnpartial` for flagging all undeclared partial
  functions, without error.
* New termination checker supporting mutually recursive definitions.
* Added `:load` command to REPL, for loading a new file
* Added `:module` command to REPL, for adding modules
* Renamed library modules (now have initial capital)

## Internal changes

* Several improvements and fixes to unification
* Added collapsing optimisation and more aggressive erasure

# New in 0.9.4:

## User visible changes

* Simple packaging system
* Added `--dumpc` flag for displaying generated code

## Internal changes

* Improve overloading resolution (especially where this is a type error)
* Various important bug fixes with evaluation and compilation
* More aggressive compile-time evaluation

# New in 0.9.3

## User visible changes

* Added binding forms to syntax rules
* Named class instances
* Added `:set` command, with options `errorcontext` for displaying local
  variables in scope when a unification error occurs, and `showimplicits`
  for displaying elaborated terms in full
* Added `--errorcontext` command line switch
* Added `:proofs` and `:rmproofs` commands
* Various minor REPL improvements and fixes

## Internal changes

* Completely new run time system (not based on Epic or relying on Boehm GC)
* Normalise before forcing to catch more forceable arguments
* Types no longer exported in normal form
* Try to resolve overloading by inspecting types, rather than full type
  checking

# New in 0.9.2

## User visible changes

* backtick notation added: ``x `foo` y  ==> foo x y``
* case expressions allowed in type signatures
* Library extensions in prelude.vect and prelude.algebra
* `malloc`/`trace_malloc` added to builtins.idr

## Internal changes

* Some type class resolution fixes
* Several minor bug fixes
* Performance improvements in resolving overloading and type classes

# New in 0.9.1

## User visible changes

* DSL notation, for overloading lambda and let bindings
* Dependent records, with projection and update
* Totality checking and `total` keyword
* Auto implicits and default argument values `{auto n : T}`, `{default val n : T}`
* Overlapping type class instances disallowed
* Many extensions to `prelude.nat` and `prelude.list` libraries (mostly thanks to
  Dominic Mulligan)
* New libraries: `control.monad.identity`, `control.monad.state`
* Small improvements in error reporting

## Internal changes

* Faster compilation (only compiling names which are used)
* Better type class resolution
* Lots of minor bug fixes

# 0.1.x to 0.9.0

Complete rewrite.

## User visible changes

* New proof/tactics syntax
* New syntax for pairs/dependent pairs
* Indentation-significant syntax
* Added type classes
* Added where clauses
* Added case expressions, pattern matching let and lambda
* Added monad comprehensions
* Added cumulativity and universe checking
* Ad-hoc name overloading
  - Resolved by type or explicit namespace
* Modules (Haskell-style)
* public, abstract and private access to functions and types
* Separate type-checking
* Improved interactive environment
* Replaced 'do using' with Monad class
* Extended syntax macros

## Internal changes

* Everything :-)
* All definitions (functions, classes and instances) are elaborated to top
  level, fully explicit, data declarations and pattern matching definitions,
  which are verified by a minimal type checker.

This is the first release of a complete reimplementation. There will be bugs.
If you find any, please do not hesitate to contact Edwin Brady
(ecb10@st-andrews.ac.uk).

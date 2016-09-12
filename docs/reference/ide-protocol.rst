********************
The IDE Protocol
********************

The Idris REPL has two modes of interaction: a human-readable syntax designed for direct use in a terminal, and a machine-readable syntax designed for using Idris as a backend for external tools.

Protocol Overview
-----------------

The communication protocol is of asynchronous request-reply style: a single request from the client is handled by Idris at a time.
Idris waits for a request on its standard input stream, and outputs the answer or answers to standard output.
The result of a request can be either success, failure, or intermediate output; and furthermore, before the result is delivered, there might be additional meta-messages.


A reply can consist of multiple messages: any number of messages to inform the user about the progress of the request or other informational output, and finally a result, either ``ok`` or ``error``.

The wire format is the length of the message in characters, encoded in 6 characters hexadecimal, followed by the message encoded as S-expression (sexp).
Additionally, each request includes a unique integer (counting upwards), which is repeated in all messages corresponding to that request.

An example interaction from loading the file ``/home/hannes/empty.idr`` looks as follows on the wire:::

  00002a((:load-file "/home/hannes/empty.idr") 1)
  000039(:write-string "Type checking /home/hannes/empty.idr" 1)
  000025(:set-prompt "/home/hannes/empty" 1)
  000032(:return (:ok "Loaded /home/hannes/empty.idr") 1)


The first message is the request from idris-mode to load the specific file, which length is hex 2a, decimal 42 (including the newline at the end).
The request identifier is set to 1.
The first message from Idris is to write the string ``Type checking /home/hannes/empty.idr``, another is to set the prompt to ``*/home/hannes/empty``.
The answer, starting with ``:return`` is ``ok``, and additional information is that the file was loaded.

There are three atoms in the wire language: numbers, strings, and symbols.
The only compound object is a list, which is surrounded by parenthesis.
The syntax is::

  A ::= NUM | '"' STR '"' | ':' ALPHA+
  S ::= A | '(' S* ')' | nil

where ``NUM`` is either 0 or a positive integer, ``ALPHA`` is an alphabetical character, and ``STR`` is the contents of a string, with ``"`` escaped by a backslash.
The atom ``nil`` is accepted instead of ``()`` for compatibility with some regexp pretty-printing routines.

The state of the Idris process is mainly the active file, which needs to be kept synchronised between the editor and Idris.
This is achieved by the already seen ``:load-file`` command.

The available commands include:

  ``(:load-file FILENAME)``
    Load the named file.

  ``(:interpret STRING)``
    Interpret ``STRING`` at the Idris REPL, returning a highlighted result.

  ``(:repl-completions STRING)``
    Return the result of tab-completing ``STRING`` as a REPL command.

  ``(:type-of STRING)``
    Return the type of the name, written with Idris syntax in the ``STRING``.
    The reply may contain highlighting information.

  ``(:case-split LINE NAME)``
    Generate a case-split for the pattern variable ``NAME`` on program line ``LINE``.
    The pattern-match cases to be substituted are returned as a string with no highlighting.

  ``(:add-clause LINE NAME)``
    Generate an initial pattern-match clause for the function declared as ``NAME`` on program line ``LINE``.
    The initial clause is returned as a string with no highlighting.

  ``(:add-proof-clause LINE NAME)``
    Add a clause driven by the ``<==`` syntax.

  ``(:add-missing LINE NAME)``
    Add the missing cases discovered by totality checking the function declared as ``NAME`` on program line ``LINE``.
    The missing clauses are returned as a string with no highlighting.

  ``(:make-with LINE NAME)``
    Create a with-rule pattern match template for the clause of function ``NAME`` on line ``LINE``.
    The new code is returned with no highlighting.

  ``(:make-case LINE NAME)``
    Create a case pattern match template for the clause of function ``NAME`` on line ``LINE``.
    The new code is returned with no highlighting.

  ``(:make-lemma LINE NAME)``
    Create a top level function with a type which solves the hole named ``NAME`` on line ``LINE``.

  ``(:proof-search LINE NAME HINTS)``
    Attempt to fill out the holes on ``LINE`` named ``NAME`` by proof search.
    ``HINTS`` is a possibly-empty list of additional things to try while searching.

  ``(:docs-for NAME)``
    Look up the documentation for ``NAME``, and return it as a highlighted string.

  ``(:metavariables WIDTH)``
    List the currently-active holes, with their types pretty-printed with ``WIDTH`` columns.

  ``(:who-calls NAME)``
    Get a list of callers of ``NAME``.

  ``(:calls-who NAME)``
    Get a list of callees of ``NAME``.

  ``(:browse-namespace NAMESPACE)``
    Return the contents of ``NAMESPACE``, like ``:browse`` at the command-line REPL.

  ``(:normalise-term TM)``
    Return a highlighted string consisting of the results of normalising the serialised term ``TM`` (which would previously have been sent as the ``tt-term`` property of a string).

  ``(:show-term-implicits TM)``
    Return a highlighted string consisting of the results of making all arguments in serialised term ``TM`` (which would previously have been sent as the ``tt-term`` property of a string) explicit.

  ``(:hide-term-implicits TM)``
    Return a highlighted string consisting of the results of making all arguments in serialised term ``TM`` (which would previously have been sent as the ``tt-term`` property of a string) follow their usual implicitness setting.

  ``(:elaborate-term TM)``
    Return a highlighted string consisting of the the core language term corresponding to serialised term ``TM`` (which would previously have been sent as the ``tt-term`` property of a string).

  ``(:print-definition NAME)``
    Return the definition of ``NAME`` as a highlighted string.

  ``(:repl-completions NAME)``
    Search names, types and documentations which contain ``NAME``.

  ``(:version UID)``
    Return the version information of the Idris compiler.



Possible replies include a normal final reply:::

 (:return (:ok SEXP [HIGHLIGHTING]))
 (:return (:error String [HIGHLIGHTING]))

A normal intermediate reply:::

 (:output (:ok SEXP [HIGHLIGHTING]))
 (:output (:error String [HIGHLIGHTING]))

Informational and/or abnormal replies:::

  (:write-string String)
  (:set-prompt String)
  (:warning (FilePath (LINE COL) (LINE COL) String [HIGHLIGHTING]))

Proof mode replies:::

  (:start-proof-mode)
  (:write-proof-state [String] [HIGHLIGHTING])
  (:end-proof-mode)
  (:write-goal String)

Output Highlighting
-------------------

Idris mode supports highlighting the output from Idris.
In reality, this highlighting is controlled by the Idris compiler.
Some of the return forms from Idris support an optional extra parameter: a list mapping spans of text to metadata about that text.
Clients can then use this list both to highlight the displayed output and to enable richer interaction by having more metadata present.
For example, the Emacs mode allows right-clicking identifiers to get a menu with access to documentation and type signatures.


A particular semantic span is a three element list.
The first element of the list is the index at which the span begins, the second element is the number of characters included in the span, and the third is the semantic data itself.
The semantic data is a list of lists.
The head of each list is a key that denotes what kind of metadata is in the list, and the tail is the metadata itself.

The following keys are available:
  ``name``
    gives a reference to the fully-qualified Idris name
  ``implicit``
    provides a Boolean value that is True if the region is the name of an implicit argument
  ``decor``
    describes the category of a token, which can be ``type``, ``function``, ``data``, ``keyword``, or ``bound``.

  ``source-loc``
    states that the region refers to a source code location. Its body is a collection of key-value pairs, with the following possibilities:

    ``filename``
      provides the filename

    ``start``
      provides the line and column that the source location starts at as a two-element tail

    ``end``
      provides the line and column that the source location ends at as a two-element tail

  ``text-formatting``
    provides an attribute of formatted text. This is for use with natural-language text, not code, and is presently emitted only from inline documentation. The potential values are ``bold``, ``italic``, and ``underline``.

  ``link-href``
    provides a URL that the corresponding text is a link to. 

  ``quasiquotation``
    states that the region is quasiquoted.

  ``antiquotation``
    states that the region is antiquoted.

  ``tt-term``
    A serialised representation of the Idris core term corresponding to the region of text.

Source Code Highlighting
------------------------

Idris supports instructing editors how to colour their code.
When elaborating source code or REPL input, Idris will locate regions of the source code corresponding to names, and emit information about these names using the same metadata as output highlighting.

These messages will arrive as replies to the command that caused elaboration to occur, such as ``:load-file`` or ``:interpret``.
They have the format:::

  (:output (:ok (:highlight-source POSNS)))

where ``POSNS`` is a list of positions to highlight. Each of these is a two-element list whose first element is a position (encoded as for the ``source-loc`` property above) and whose second element is highlighting metadata in the same format used for output.

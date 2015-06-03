****************************************
Semantic Highlighting & Pretty Printing
****************************************

Since ``v0.9.18`` Idris comes with support for semantic highlighting.
When using the ``REPL`` or IDE support, Idris will highlight your code accordingly to its meaning within the Idris structure. A precursor to semantic highlighting support is the pretty printing of definitions to console, LaTeX, or HTML.

The default styling scheme used was inspired by Conor McBride's own set of stylings, informally known as *Conor Colours*.


Legend
======

The concepts and their default stylings are as follows:

+----------------+---------------+----------------+----------------+
| Idris Term     | HTML          | LaTeX          | IDE/REPL       |
+================+===============+================+================+
| Bound Variable | Purple        | Magenta        |                |
+----------------+---------------+----------------+----------------+
| Keyword        | Bold          | Underlined     |                |
+----------------+---------------+----------------+----------------+
| Function       | Green         | Green          |                |
+----------------+---------------+----------------+----------------+
| Type           | Blue          | Blue           |                |
+----------------+---------------+----------------+----------------+
| Data           | Red           | Red            |                |
+----------------+---------------+----------------+----------------+
| Implicit       | Italic Purple | Italic Magenta |                |
+----------------+---------------+----------------+----------------+

Pretty Printing
===============

Idris also supports the pretty printing of code to HTML and LaTeX using the commands:

+ ``:pp <latex|html> <width> <function name>``
+ ``:pprint <latex|html> <width> <function name>``


Customisation
=============

If you are not happy with the colours used, the VIM and Emacs editor support allows for customisation of the colours. When pretty printing Idris code as LaTeX and HTML, commands and a CSS style are provided. The colours used by the REPL can be customised through the initialisation script.


Further Information
===================

Please also see the `Idris Extras <https://github.com/idris-hackers/idris-extras>`_ project for links to editor support, and pre-made style files for LaTeX and HTML.

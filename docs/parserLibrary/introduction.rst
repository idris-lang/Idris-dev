.. _parserLibraryIntro:

***************************
Parser Library Introduction
***************************

The parser library is used in a similar way to Parsec which is a library for writing parsers in Haskell. It is based on higher-order parser combinators, so a complicated parser can be made out of many smaller ones.

.. list-table::

  * - This is a two stage process:
        - Lexer - This takes the input string and turns it into a list of Tokens.
        - Parser - This takes the list of tokens and outputs the code.

.. image:: ../image/parserTopLevel.png
   :width: 484px
   :height: 147px
   :alt: diagram illustrating these stages of lexer and parser

The advantage of using two stages, like this, is that things like whitespace and comments don't need to be considered in every parser rule.

The  Idris parser library differs from Parsec in that you need to say in the Recogniser whether a rule is guaranteed to consume input. This means that the Idris type system prevents the construction of recognisers/rules that can't consume the input.

The Lexer is similar but works at the level of characters rather than tokens, and you need to provide a TokenMap which says how to build a token representation from a string when a rule is matched.




.. image:: ../image/parserModules.png
   :width: 484px
   :height: 147px
   :alt: diagram illustrating these stages of lexer and parser





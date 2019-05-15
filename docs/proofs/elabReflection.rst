Extending Idris using Elaborator Reflection
===========================================

Idris provides a mechanism to modify the language without having to recompile Idris itself. We can think of this in terms of metaprogramming or domain specific languages or just building in new capabilities.

In order to extend the language we need to know something about how Idris is complied. This page explains only what is needed to customise the elaboration. For more information about the compiler's implementation see `Edwin Brady's 2013 paper`_ and for customising the elaboration process see `Elaborator reflection: extending Idris in Idris`_ and `David Christiansen's PhD thesis`_ .

Here is a diagram of the multistage process at the top level when Idris code gets compiled:

.. image:: ../image/idrisTopLevel.png
   :width: 484px
   :height: 147px

TT is a core language which is syntactically very simple, this makes it easy for computers to process but very verbose and hard for humans to read. This elaboration is done by a logic language (proof tactics) similar to LTac in Coq. Here the word 'tactics' is used to refer to these elaboration tactics - not to be confused with the old tactics mechanism.

.. image:: ../image/compareToProofAssist.png
   :width: 229px
   :height: 114px

This gives the opportunity to allow the primitives of the elaboration mechanism  to be exposed to metaprograms.
During elaboration TT (Raw) structure contains:

- holes - terms yet to be inferred.
- guesses - Suppresses β-reduction while precise structure not known.

Type checker:

- include universe levels
- distinguish between global and local bound names.

.. image:: ../image/elabOverview.png
   :width: 268px
   :height: 219px

As already mentioned the TT core language is kept syntactically very simple. Part of the reason for this is that its correctness is already well proven using logic. For instance, here are the binders in TT with corresponding code and logic type introduction rules:

.. image:: ../image/binders.png
   :width: 310px
   :height: 203px

.. list-table::

   * - There is an elaborator for both definitions and terms, the definition elaborator calls the term elaborator when required.
     - .. image:: ../image/elab.png
          :width: 141px
          :height: 145px

.. target-notes::
.. _`Edwin Brady's 2013 paper`: https://eb.host.cs.st-andrews.ac.uk/drafts/impldtp.pdf
.. _`David Christiansen's PhD thesis`: https://davidchristiansen.dk/david-christiansen-phd.pdf
.. _`Elaborator reflection: extending Idris in Idris`: https://dl.acm.org/citation.cfm?doid=2951913.2951932





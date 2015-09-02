.. _sect-further:

***************
Further Reading
***************

This tutorial has given an introduction to writing and reasoning about
side-effecting programs in Idris, using the ``Effects`` library.
More details about the *implementation* of the library, such as how
``run`` works, how handlers are invoked, etc, are given in a separate
paper [1]_.

Some libraries and programs which use ``Effects`` can be found in the
following places:

-  https://github.com/edwinb/SDL-idris — some bindings for the SDL media
   library, supporting graphics in particular.

-  https://github.com/edwinb/idris-demos — various demonstration
   programs, including several examples from this tutorial, and a “Space
   Invaders” game.

-  https://github.com/SimonJF/IdrisNet2 — networking and socket
   libraries.

-  https://github.com/edwinb/Protocols — a high level communication
   protocol description language.

The inspiration for the ``Effects`` library was Bauer and Pretnar’s
Eff language [2]_, which describes a language based on algebraic
effects and handlers.  Other recent languages and libraries have also
been built on this ideas, for example [3]_ and [4]_. The theoretical
foundations are also well-studied see [5]_, [6]_, [7]_, [8]_.



.. [1] Edwin Brady. 2013. Programming and reasoning with algebraic
       effects and dependent types. SIGPLAN Not. 48, 9 (September
       2013), 133-144. DOI=10.1145/2544174.2500581
       https://dl.acm.org/citation.cfm?doid=2544174.2500581

.. [2] Andrej Bauer, Matija Pretnar, Programming with algebraic
       effects and handlers, Journal of Logical and Algebraic Methods
       in Programming, Volume 84, Issue 1, January 2015, Pages
       108-123, ISSN 2352-2208,
       http://math.andrej.com/wp-content/uploads/2012/03/eff.pdf


.. [3] Ben Lippmeier. 2009. Witnessing Purity, Constancy and
       Mutability. In Proceedings of the 7th Asian Symposium on
       Programming Languages and Systems (APLAS '09), Zhenjiang Hu
       (Ed.). Springer-Verlag, Berlin, Heidelberg,
       95-110. DOI=10.1007/978-3-642-10672-9_9
       http://link.springer.com/chapter/10.1007%2F978-3-642-10672-9_9


.. [4] Ohad Kammar, Sam Lindley, and Nicolas Oury. 2013. Handlers in
       action. SIGPLAN Not. 48, 9 (September 2013),
       145-158. DOI=10.1145/2544174.2500590
       https://dl.acm.org/citation.cfm?doid=2544174.2500590

.. [5] Martin Hyland, Gordon Plotkin, John Power, Combining effects:
       Sum and tensor, Theoretical Computer Science, Volume 357,
       Issues 1–3, 25 July 2006, Pages 70-99, ISSN 0304-3975,
       (https://www.sciencedirect.com/science/article/pii/S0304397506002659)

.. [6] Paul Blain Levy. 2004. Call-By-Push-Value: A
       Functional/Imperative Synthesis (Semantics Structures in
       Computation, V. 2). Kluwer Academic Publishers, Norwell, MA,
       USA.

.. [7] Plotkin, Gordon, and Matija Pretnar. "Handlers of algebraic
       effects." Programming Languages and Systems. Springer Berlin
       Heidelberg, 2009. 80-94.

.. [8] Pretnar, Matija. "Logic and handling of algebraic effects." (2010).

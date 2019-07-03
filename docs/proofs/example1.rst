Elaborator Reflection - Identity Example
========================================

.. list-table::

   * - This example of elaborator reflection steps through this metaprogram that generates the identity function:
     - .. code-block:: idris

         %language ElabReflection

         idNat : Nat -> Nat
         idNat = %runElab (do intro `{{x}}
                              fill (Var `{{x}})
                              solve)

.. list-table::
   :widths: 200 100

   * - At the beginning of executing the elaboration script, the initial state consists of a single hole of type Nat -> Nat.

       As a first approximation, the state consists of a term with holes in it, an indicator of which hole is focused, a queue of the next holes to focus on, and miscellaneous information like a source of fresh names. The intro tactic modifies this state, replacing the focused hole with a lambda and focusing on the lambda's body.
     - .. image:: ../image/tree.png
          :width: 133px
          :height: 106px

The following is a walkthough looking at the state after each tactic:

.. list-table::

   * - Start with the type signature like this:
     - .. code-block:: idris

         %language ElabReflection

         idNat : Nat -> Nat
         idNat = %runElab (do

   * - In order to investigate how the program works this table shows the proof state at each stage as the tactics are applied. So here is the proof state at the start:
     - .. image:: ../image/elabProofStateEx1_1.png
          :width: 310px
          :height: 115px

   * - This table shows the hole types and what they depend on. The aim is to illustrate the types by analogy with proofs, as a line with the premises above it and the conclusion below it.
     - .. image:: ../image/elabLogicEx1_1.png
          :width: 277px
          :height: 15px

   * - The term is:
     - ?{hole_0} ≈ ? {hole_2} . {hole_2} . {hole_0}

   * - It is possible to read the state from the script by calling getEnv, getGoal and getHoles. To show the results I hacked this: `my code`_.

     - .. code-block:: idris

         getEnv=[]

         getGoal=({hole_2}, {TT:Bind
            name=`{{__pi_arg}}
            binder={
               Π ({`{{Nat}}.["Nat", "Prelude"]}:{type const tag=8,0}).{
                  TT:TType tt=ext=./Prelude/Nat.idr#20
               }
            }
            tt={
               TT:Parameter name ref
               NameType={type const tag=8,0}
               TTName={`{{Nat}}.["Nat","Prelude"]}
               TT={TT:TType
                  tt=ext=./Prelude/Nat.idr#20
               }
            }
         })

         getHoles=[{hole_2},{hole_0}]

   * - getGuess
     - error no guess

   * - Introduce a lambda binding around the current hole and focus on the body.
     - intro \`{{x}}

   * - The state now looks like this:
     - .. image:: ../image/elabProofStateEx1_2.png
          :width: 312px
          :height: 84px

   * - The hole types now looks like this:
     - .. image:: ../image/elabLogicEx1_2.png
          :width: 279px
          :height: 26px

   * - The term now looks like this:
     - ?{hole_0} ≈ λ x . ? {hole_2} . {hole_2} . {hole_0}

   * - Again we can check the state by calling getEnv, getGoal and getHoles: see `my code`_

     - .. code-block:: idris

         getEnv=[(
           `{{x}}, {
              λ ({`{{Nat}}.["Nat", "Prelude"]}:{type const tag=8,0}).
              {TT:TType
                  tt=ext=./Prelude/Nat.idr#20
              }
           }
         )]

         getGoal=({hole_2},{
           TT:Parameter name ref
             NameType={type const tag=8,0}
           TTName={`{{Nat}}.["Nat", "Prelude"]}
           TT={TT:TType
               tt=ext=./Prelude/Nat.idr#20
            }
          }
          )

          getHoles=[{hole_2},{hole_0}]

   * - getGuess
     - error no guess

   * - Place a term into a hole, unifying its type
     - fill (Var \`{{x}})

   * - The state still looks like this:
     - .. image:: ../image/elabProofStateEx1_3.png
          :width: 312px
          :height: 57px

   * - The hole types now looks like this:
     - .. image:: ../image/elabLogicEx1_3.png
          :width: 290px
          :height: 26px

   * - The term now looks like this:
     - ?{hole_0} ≈ λ x . ?{hole_2} ≈ x . {hole_2} . {hole_0}

   * - Again we can check the state by calling getEnv, getGoal and getHoles: see `my code`_

     - .. code-block:: idris

         getEnv=[(`{{x}}, {λ ({`{{Nat}}.["Nat", "Prelude"]}:
           {type const tag=8,0}).
             {TT:TType
               tt=ext=./Prelude/Nat.idr#20
             }
           }
         )]

         getGoal=({hole_2},
           {TT:Parameter name ref
              NameType={type const tag=8,0}
             TTName={`{{Nat}}.["Nat", "Prelude"]}
           TT={TT:TType
             tt=ext=./Prelude/Nat.idr#20
           }
         })

         getHoles=[{hole_2}, {hole_0}]

   * - getGuess
     - .. code-block:: idris

         {TT:Parameter name ref
            NameType=NameType just bound by intro
            TTName=`{{x}}
            TT={TT:Parameter name ref
               NameType={type const tag=8,0}
               TTName={`{{Nat}}.["Nat", "Prelude"]}
               TT={TT:TType
                  tt=ext=./Prelude/Nat.idr#20
               }
            }
         }

   * - Substitute a guess into a hole.
     - solve

   * - The hole types now looks like this:
     - .. image:: ../image/elabLogicEx1_4.png
          :width: 131px
          :height: 14px

   * - The term now looks like this:
     - ?{hole_0} ≈ λ x . x . {hole_0}

   * - getEnv

       getGoal

       getHoles

     - .. code-block:: idris

         getEnv=[]

         getGoal=({hole_0}, {TT:Bind
            name=`{{__pi_arg}}
            binder={
               Π ({`{{Nat}}.["Nat", "Prelude"]}:
                  {type const tag=8,0}).{TT:TType
                     tt=ext=./Prelude/Nat.idr#20
               }
            }
            tt={TT:Parameter name ref
               NameType={type const tag=8,0}
               TTName={`{{Nat}}.["Nat","Prelude"]}
               TT={TT:TType tt=ext=./Prelude/Nat.idr#20}
            }
         })

         getHoles=[{hole_0}]

   * - getGuess
     - .. code-block:: idris

         {TT:Bind
            name=`{{x}}
            binder={λ ({`{{Nat}}.["Nat","Prelude"]}:{type const tag=8,0}).{
             TT:TType
               tt=ext=./Prelude/Nat.idr#20
             }
            }
            tt={TT:Parameter name ref
               NameType=NameType just bound by intro
               TTName=`{{x}}
               TT={TT:Parameter name ref
                  NameType={type const tag=8,0}
                  TTName={`{{Nat}}.["Nat", "Prelude"]}
                  TT={TT:TType
                     tt=ext=./Prelude/Nat.idr#20
                  }
               }
            }
         }

.. target-notes::
.. _`my code`: https://github.com/martinbaker/Idris-dev/blob/uglyTTPrinter/libs/prelude/Language/Reflection/TTPrinter.idr

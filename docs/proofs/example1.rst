Example 1
=========

.. list-table:: Nat identity

   * - As an example of elaborator reflection here we step through this identity implementation:
     - Nat identity.

       .. code-block:: idris

         %language ElabReflection

         idNat : Nat -> Nat
         idNat = %runElab (do
           intro `{{x}}
           fill (Var `{{x}})
           solve
         )

.. list-table:: Nat identity

   * - We start off with a hole for the whole term (of type Nat->Nat).
       We fill that with 'intro' which creates a lambda term with a hole for the  expression.
     - diagram

       .. image:: ../image/tree.png
          :width: 133px
          :height: 106px

After each tactic we will look at the state:

.. list-table:: evolution of state

   * - We start with the type signature like this:
     - Nat identity.

       .. code-block:: idris

         %language ElabReflection

         idNat : Nat -> Nat
         idNat = %runElab (do

   * - In order to investigate how the program works we can look at the proofState at each stage as the tactics are applied. So here is the proofState at the start:
     - state

       .. image:: ../image/elabProofStateEx1_1.png
          :width: 310px
          :height: 124px

   * - We can also look at the logic at each stage: 
     - logic

       .. image:: ../image/elabLogicEx1_1.png
          :width: 126px
          :height: 33px

   * - The term is:
     - ?{hole_0} ≈ ? {hole_2} . {hole_2} . {hole_0}

   * - getEnv

       getGoal

       getHoles

     - state.

       .. code-block:: idris

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

   * - state now looks like this
     - state

       .. image:: ../image/elabProofStateEx1_2.png
          :width: 312px
          :height: 124px

   * - logic now looks like this
     - logic

       .. image:: ../image/elabLogicEx1_2.png
          :width: 126px
          :height: 45px

   * - term now looks like this
     - ?{hole_0} ≈ λ x . ? {hole_2} . {hole_2} . {hole_0}

   * - getEnv

       getGoal

       getHoles

     - state.

       .. code-block:: idris

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

   * - state now looks like this
     - state

       .. image:: ../image/elabProofStateEx1_3.png
          :width: 312px
          :height: 124px

   * - logic now looks like this
     - logic

       .. image:: ../image/elabLogicEx1_3.png
          :width: 131px
          :height: 45px

   * - term
     - ?{hole_0} ≈ λ x . ?{hole_2} ≈ x . {hole_2} . {hole_0}

   * - getEnv

       getGoal

       getHoles

     - state.

       .. code-block:: idris

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
     - state.

       .. code-block:: idris

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

   * - logic now looks like this
     - logic

       .. image:: ../image/elabLogicEx1_4.png
          :width: 131px
          :height: 14px

   * - term
     - ?{hole_0} ≈ λ x . x . {hole_0}

   * - getEnv

       getGoal

       getHoles

     - state.

       .. code-block:: idris

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
     - state.

       .. code-block:: idris

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

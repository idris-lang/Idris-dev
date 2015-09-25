  ___                   _
 /   \               _ / \      _
|  |  |             / \| |     / \
|  |  | _  _ _  _ _ \_/| | ___ \_/
| ---/ \ \/ \ \/ \ \/ \| |/   \/ \
| |  |  -/| | || | || || || | || |
| |  | |  | | |\ | /| || || | || |
\_/  \_/  \___/ \_/ \_/\_/\___/| |
                              _/ |
                             |__/
     a proof automation and program construction toolkit


Pruviloj is a library of tactics that work with Idris's elaborator
reflection. In addition to a library of small tactics, it contains
code for generating eliminators for inductive datatypes and using
those eliminators to do induction.


Q: How do I use Pruviloj?
A: Call Idris with the "-p pruviloj" option and add:
      import Pruviloj
   to the top of your file. If you want to do induction, then
   add:
      import Pruviloj.Induction
   as well.


Q: How do I find out what's available?
A: Use ":browse Pruviloj.Core" after importing the library.
   Pruviloj.Induction exports only one name: "induction".
   Use ":doc" to read the built-in documentation.


Q: How do I use the tactics?
A: Please read the Idris documentation on elaborator reflection.
   The syntax to invoke a tactic script is "%runElab script". To
   interactively work with a hole, use ":elab holeName".


Q: Where does the name come from?
A: "Pruviloj" is Esperanto for "proof tools". The stress goes on
   the penultimate syllable, and in IPA the pronunciation is written
   [pruˈvi.loi̯]. Perhaps confusingly for Esperantists, the Pruviloj
   library also contains utilities for code generation.

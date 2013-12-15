module Main

import Syntax.PreorderReasoning
import Control.Isomorphism

stupidProof : Iso (Either a b) (Either a b)
stupidProof {a} {b} = (Either a b) ={ eitherComm }=
                      (Either b a) ={ eitherComm }=
                      (Either a b) QED

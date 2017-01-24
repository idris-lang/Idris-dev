module Idris.REPL.Commands where

import Idris.AbsSyntaxTree
import Idris.Colours
import Idris.Core.TT

-- | REPL commands
data Command = Quit
             | Help
             | Eval PTerm
             | NewDefn [PDecl] -- ^ Each 'PDecl' should be either a type declaration (at most one) or a clause defining the same name.
             | Undefine [Name]
             | Check PTerm
             | Core PTerm
             | DocStr (Either Name Const) HowMuchDocs
             | TotCheck Name
             | Reload
             | Watch
             | Load FilePath (Maybe Int) -- up to maximum line number
             | RunShellCommand FilePath
             | ChangeDirectory FilePath
             | ModImport String
             | Edit
             | Compile Codegen String
             | Execute PTerm
             | ExecVal PTerm
             | Metavars
             | Prove Bool Name -- ^ If false, use prover, if true, use elab shell
             | AddProof (Maybe Name)
             | RmProof Name
             | ShowProof Name
             | Proofs
             | Universes
             | LogLvl Int
             | LogCategory [LogCat]
             | Verbosity Int
             | Spec PTerm
             | WHNF PTerm
             | TestInline PTerm
             | Defn Name
             | Missing Name
             | DynamicLink FilePath
             | ListDynamic
             | Pattelab PTerm
             | Search [String] PTerm
             | CaseSplitAt Bool Int Name
             | AddClauseFrom Bool Int Name
             | AddProofClauseFrom Bool Int Name
             | AddMissing Bool Int Name
             | MakeWith Bool Int Name
             | MakeCase Bool Int Name
             | MakeLemma Bool Int Name
             | DoProofSearch Bool   -- update file
                             Bool   -- recursive search
                             Int    -- depth
                             Name   -- top level name
                             [Name] -- hints
             | SetOpt Opt
             | UnsetOpt Opt
             | NOP
             | SetColour ColourType IdrisColour
             | ColourOn
             | ColourOff
             | ListErrorHandlers
             | SetConsoleWidth ConsoleWidth
             | SetPrinterDepth (Maybe Int)
             | Apropos [String] String
             | WhoCalls Name
             | CallsWho Name
             | Browse [String]
             | MakeDoc String -- IdrisDoc
             | Warranty
             | PrintDef Name
             | PPrint OutputFmt Int PTerm
             | TransformInfo Name
             -- Debugging commands
             | DebugInfo Name
             | DebugUnify PTerm PTerm

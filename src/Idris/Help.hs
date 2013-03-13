module Idris.Help (CmdArg(..), help) where

data CmdArg = ExprArg -- ^ The command takes an expression
            | NameArg -- ^ The command takes a name
            | FileArg -- ^ The command takes a file
            | ModuleArg -- ^ The command takes a module name
            | OptionArg -- ^ The command takes an option
            | MetaVarArg -- ^ The command takes a metavariable
            | NoArg -- ^ No completion yet


help :: [([String], String, String, CmdArg)]
help =
  [ (["<expr>"], "", "Evaluate an expression", NoArg),
    ([":t"], "<expr>", "Check the type of an expression", ExprArg),
    ([":miss", ":missing"], "<name>", "Show missing clauses", NameArg),
    ([":i", ":info"], "<name>", "Display information about a type class", NameArg),
    ([":total"], "<name>", "Check the totality of a name", NameArg),
    ([":r",":reload"], "", "Reload current file", NoArg),
    ([":l",":load"], "<filename>", "Load a new file", FileArg),
    ([":m",":module"], "<module>", "Import an extra module", ModuleArg), -- NOTE: dragons
    ([":e",":edit"], "", "Edit current file using $EDITOR or $VISUAL", NoArg),
    ([":m",":metavars"], "", "Show remaining proof obligations (metavariables)", MetaVarArg),
    ([":p",":prove"], "<name>", "Prove a metavariable", MetaVarArg),
    ([":a",":addproof"], "<name>", "Add proof to source file", NameArg),
    ([":rmproof"], "<name>", "Remove proof from proof stack", NameArg),
    ([":showproof"], "<name>", "Show proof", NameArg),
    ([":proofs"], "", "Show available proofs", NoArg),
    ([":c",":compile"], "<filename>", "Compile to an executable <filename>", FileArg),
    ([":js", ":javascript"], "<filename>", "Compile to JavaScript <filename>", FileArg),
    ([":exec",":execute"], "", "Compile to an executable and run", NoArg),
    ([":?",":h",":help"], "", "Display this help text", NoArg),
    ([":set"], "<option>", "Set an option (errorcontext, showimplicits)", OptionArg),
    ([":unset"], "<option>", "Unset an option", OptionArg),
    ([":q",":quit"], "", "Exit the Idris system", NoArg)
  ]
